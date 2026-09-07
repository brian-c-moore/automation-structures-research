//! Step-based graph modality (docs/execution-modalities.md).
//!
//! Arbitrary DAG topology: predecessors are computed from
//! `workload.edges()` (not from index arithmetic). Each operator
//! advances through `OperatorState::NotReady -> Ready -> Running ->
//! Completed`. The driver picks the lowest-`OpId` Ready operator on
//! each step for determinism (`BTreeMap` keying, not `HashMap`).
//!
//! On a graph that cannot be advanced (a cycle), the driver returns
//! `Err(StepGraphError::CycleDetected)` rather than panicking. The
//! Workload's `assert_workload_well_formed` validator rejects cyclic
//! graphs at construction unless `compatible_modalities` is
//! `&[StreamGraph]`.

use crate::policies::ConfigVector;
use crate::primitives::operator::OperatorState;
use crate::workloads::{Operator, OperatorFactory, Workload};
use std::collections::BTreeMap;

#[derive(Debug)]
pub enum StepGraphError {
    /// No operator is eligible to advance and not all operators are
    /// Completed. The workload graph has a cycle that StepGraph cannot
    /// execute. Workloads whose graph contains cycles must exclude
    /// `Modality::StepGraph` from `compatible_modalities()`.
    CycleDetected { stuck_ids: Vec<String> },
}

/// Step-graph driver. It consults `cv.invocation` for per-batch
/// ordering at each node (the same reorder logic Sequential applies). The other four fields are not
/// interpreted: graph topology comes from `workload.edges()`, node
/// identity is `OpId`, factories are fixed, and an operator completes
/// after its one bounded drain.
pub fn run_step_graph<W: Workload>(
    workload: &W,
    cv: &ConfigVector,
) -> Result<W::Output, StepGraphError>
where
    W::OpId: Ord,
{
    let operators = workload.operators();
    let edges = workload.edges();
    let initial = workload.initial_inputs();

    let mut state: BTreeMap<W::OpId, OperatorState> = operators
        .iter()
        .map(|(id, _)| (id.clone(), OperatorState::NotReady))
        .collect();

    let mut input_buffer: BTreeMap<W::OpId, Vec<W::Record>> = BTreeMap::new();
    let mut output_buffer: BTreeMap<W::OpId, Vec<W::Record>> = BTreeMap::new();

    let predecessors = compute_predecessors::<W>(&edges);
    let successors = compute_successors::<W>(&edges);

    for (id, _) in &operators {
        if predecessors.get(id).map(|p| p.is_empty()).unwrap_or(true) {
            state.insert(id.clone(), OperatorState::Ready);
            let init = initial.get(id).cloned().unwrap_or_default();
            input_buffer.insert(id.clone(), init);
        }
    }

    let factories: BTreeMap<W::OpId, OperatorFactory<W::Record>> = operators.into_iter().collect();

    loop {
        let mut advanced = false;

        // Promote NotReady -> Ready when all predecessors are Completed.
        let ids: Vec<W::OpId> = state.keys().cloned().collect();
        for id in &ids {
            if let Some(OperatorState::NotReady) = state.get(id) {
                let preds = predecessors.get(id).cloned().unwrap_or_default();
                let all_completed = preds
                    .iter()
                    .all(|p| matches!(state.get(p), Some(OperatorState::Completed)));
                if all_completed {
                    // Clone-read rather than remove, so fan-out predecessors
                    // can serve multiple successors. Removing would silently
                    // lose records for the second-and-later consumer in a
                    // diamond; the diamond unit test below covers that case.
                    let mut collected: Vec<W::Record> = Vec::new();
                    for p in &preds {
                        if let Some(out) = output_buffer.get(p) {
                            collected.extend(out.iter().cloned());
                        }
                    }
                    input_buffer.insert(id.clone(), collected);
                    state.insert(id.clone(), OperatorState::Ready);
                    advanced = true;
                }
            }
        }

        // Pick the lowest-OpId Ready operator, run it, mark Completed.
        let ready: Option<W::OpId> = state.iter().find_map(|(id, s)| {
            if matches!(s, OperatorState::Ready) {
                Some(id.clone())
            } else {
                None
            }
        });
        if let Some(id) = ready {
            let factory = factories.get(&id).expect("factory exists");
            let mut op: Box<dyn Operator<W::Record>> = factory();
            let inputs = input_buffer.remove(&id).unwrap_or_default();
            // Per-batch reorder per cv.invocation: StepGraph orders each
            // node's batch on consumption.
            let inputs = cv.invocation.reorder_batch(inputs, |_| 0i64);
            let mut out: Vec<W::Record> = Vec::new();
            for r in inputs {
                out.extend(op.on_record(r));
            }
            out.extend(op.on_end_of_stream());
            output_buffer.insert(id.clone(), out);
            state.insert(id, OperatorState::Completed);
            advanced = true;
        }

        if state
            .values()
            .all(|s| matches!(s, OperatorState::Completed))
        {
            break;
        }

        if !advanced {
            let stuck: Vec<String> = state
                .iter()
                .filter(|(_, s)| !matches!(s, OperatorState::Completed))
                .map(|(id, _)| format!("{:?}", id))
                .collect();
            return Err(StepGraphError::CycleDetected { stuck_ids: stuck });
        }
    }

    let sinks: BTreeMap<W::OpId, Vec<W::Record>> = state
        .keys()
        .filter(|id| successors.get(id).map(|s| s.is_empty()).unwrap_or(true))
        .filter_map(|id| output_buffer.remove(id).map(|out| (id.clone(), out)))
        .collect();
    Ok(workload.reduce(sinks.into_iter().collect()))
}

fn compute_predecessors<W: Workload>(
    edges: &[(W::OpId, W::OpId)],
) -> BTreeMap<W::OpId, Vec<W::OpId>> {
    let mut m: BTreeMap<W::OpId, Vec<W::OpId>> = BTreeMap::new();
    for (from, to) in edges {
        m.entry(to.clone()).or_default().push(from.clone());
    }
    m
}

fn compute_successors<W: Workload>(
    edges: &[(W::OpId, W::OpId)],
) -> BTreeMap<W::OpId, Vec<W::OpId>> {
    let mut m: BTreeMap<W::OpId, Vec<W::OpId>> = BTreeMap::new();
    for (from, to) in edges {
        m.entry(from.clone()).or_default().push(to.clone());
    }
    m
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::modalities::Modality;
    use crate::workloads::{Operator, OperatorFactory};
    use std::collections::HashMap;

    // Diamond workload: A -> B, A -> C, B -> D, C -> D.
    // Each operator tags its records with its own id; D's collected
    // output must include records that came via both B and C.
    struct DiamondWorkload;

    struct TagOp {
        id: &'static str,
    }
    impl Operator<String> for TagOp {
        fn on_record(&mut self, r: String) -> Vec<String> {
            vec![format!("{}->{}", r, self.id)]
        }
    }

    impl Workload for DiamondWorkload {
        type Record = String;
        type Output = Vec<String>;
        type OpId = &'static str;

        fn operators(&self) -> Vec<(&'static str, OperatorFactory<String>)> {
            let mk = |id: &'static str| -> OperatorFactory<String> {
                Box::new(move || Box::new(TagOp { id }))
            };
            vec![
                ("A", mk("A")),
                ("B", mk("B")),
                ("C", mk("C")),
                ("D", mk("D")),
            ]
        }

        fn edges(&self) -> Vec<(&'static str, &'static str)> {
            vec![("A", "B"), ("A", "C"), ("B", "D"), ("C", "D")]
        }

        fn initial_inputs(&self) -> HashMap<&'static str, Vec<String>> {
            let mut m = HashMap::new();
            m.insert("A", vec!["seed".to_string()]);
            m
        }

        fn reduce(&self, sink_outputs: HashMap<&'static str, Vec<String>>) -> Vec<String> {
            let mut all: Vec<String> = sink_outputs
                .into_iter()
                .flat_map(|(_, recs)| recs)
                .collect();
            all.sort();
            all
        }

        fn compatible_modalities(&self) -> &'static [Modality] {
            &[Modality::StepGraph]
        }
    }

    #[test]
    fn diamond_routes_through_both_b_and_c() {
        let w = DiamondWorkload;
        let out = run_step_graph(&w, &ConfigVector::default_for_test()).expect("acyclic diamond");
        // D should receive records that came via B AND C. With one
        // seed record at A, A emits "seed->A" to B and to C
        // (fan-out), B emits "seed->A->B", C emits "seed->A->C", and
        // D collects both, emitting "seed->A->B->D" and
        // "seed->A->C->D".
        assert!(
            out.contains(&"seed->A->B->D".to_string()),
            "missing B-path record; got {:?}",
            out
        );
        assert!(
            out.contains(&"seed->A->C->D".to_string()),
            "missing C-path record; got {:?}",
            out
        );
        assert_eq!(
            out.len(),
            2,
            "expected exactly two D-emitted records; got {:?}",
            out
        );
    }

    // Cyclic workload: A -> B, B -> A. StepGraph must return
    // CycleDetected rather than panicking.
    struct CycleWorkload;

    struct PassOp;
    impl Operator<i64> for PassOp {
        fn on_record(&mut self, r: i64) -> Vec<i64> {
            vec![r]
        }
    }

    impl Workload for CycleWorkload {
        type Record = i64;
        type Output = i64;
        type OpId = &'static str;

        fn operators(&self) -> Vec<(&'static str, OperatorFactory<i64>)> {
            let mk = || -> OperatorFactory<i64> { Box::new(move || Box::new(PassOp)) };
            vec![("A", mk()), ("B", mk())]
        }
        fn edges(&self) -> Vec<(&'static str, &'static str)> {
            vec![("A", "B"), ("B", "A")]
        }
        fn initial_inputs(&self) -> HashMap<&'static str, Vec<i64>> {
            HashMap::new()
        }
        fn reduce(&self, _sink_outputs: HashMap<&'static str, Vec<i64>>) -> i64 {
            0
        }
        // Declare StepGraph compatibility so the driver runs and the cycle
        // detection is reached.
        fn compatible_modalities(&self) -> &'static [Modality] {
            &[Modality::StepGraph]
        }
    }

    #[test]
    fn cycle_returns_err_no_panic() {
        let w = CycleWorkload;
        match run_step_graph(&w, &ConfigVector::default_for_test()) {
            Err(StepGraphError::CycleDetected { stuck_ids }) => {
                assert_eq!(stuck_ids.len(), 2, "both A and B are stuck");
            }
            Ok(v) => panic!("expected CycleDetected, got Ok({:?})", v),
        }
    }
}
