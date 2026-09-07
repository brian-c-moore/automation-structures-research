//! Workloads expressible across the four modalities
//! (docs/execution-modalities.md).
//!
//! A workload is a pure description of operators, edges, initial
//! inputs, and a reduce step. The four modality drivers consume that
//! description and run it under their respective disciplines. No
//! workload has its own `run()` method.

pub mod actor_message_exchange;
pub mod build_dag;
pub mod data_pipeline;
pub mod reactive_ui;
pub mod render_graph;
pub mod scientific_workflow;
pub mod streaming_sql;
pub mod token_stream;

use crate::modalities::Modality;
use crate::policies::ConfigVector;
use std::collections::HashMap;

/// A single operator: consumes input records, emits output records.
/// The trait is intentionally minimal so all four modality drivers can
/// drive it uniformly.
pub trait Operator<R>: Send {
    /// Called once per input record. Returns records to emit on the
    /// operator's output edge(s). May return zero or more records.
    fn on_record(&mut self, record: R) -> Vec<R>;

    /// Called once when all upstream sources have signaled EOS. Lets
    /// stateful operators flush partial state (e.g., windowed
    /// aggregators emit their last partial window). Default: no-op.
    fn on_end_of_stream(&mut self) -> Vec<R> {
        Vec::new()
    }
}

pub type OperatorFactory<R> = Box<dyn Fn() -> Box<dyn Operator<R>> + Send + Sync>;

pub trait Workload: Send + Sync {
    type Record: Clone + Send + 'static;
    type Output: PartialEq + std::fmt::Debug;
    // Ord is required by StepGraphDriver for deterministic operator
    // selection order. Hash is kept for HashMap-based driver buffers
    // where determinism is not required (e.g., the streaming-graph
    // driver, which exercises queues, not key iteration).
    type OpId: Clone + Eq + Ord + std::hash::Hash + std::fmt::Debug + Send + 'static;

    /// The graph: each entry is (id, factory). Drivers call the
    /// factory once per execution to obtain a fresh operator instance.
    /// (Fork-join needs N copies; per-record state must not bleed
    /// across runs.)
    fn operators(&self) -> Vec<(Self::OpId, OperatorFactory<Self::Record>)>;

    /// (from, to) edges. Multiple entries with the same `to` is fan-in.
    /// Multiple entries with the same `from` is fan-out.
    fn edges(&self) -> Vec<(Self::OpId, Self::OpId)>;

    /// Initial records for each source operator (operator with no
    /// incoming edges). Operators not listed here receive no initial
    /// input and consume only from their predecessors.
    fn initial_inputs(&self) -> HashMap<Self::OpId, Vec<Self::Record>>;

    /// Reduce the sink operators' collected outputs to the workload's
    /// declared Output type. A sink operator is one with no outgoing
    /// edges. The HashMap maps sink OpId → the list of records that
    /// arrived at that sink (after the driver finishes).
    fn reduce(&self, sink_outputs: HashMap<Self::OpId, Vec<Self::Record>>) -> Self::Output;

    /// Modalities this workload supports. The harness will only run
    /// the workload through drivers in this set. A workload like
    /// `StreamingAggregation` returns &[Modality::StreamGraph]; a
    /// workload like `DataPipeline` returns all four.
    fn compatible_modalities(&self) -> &'static [Modality];

    /// Equivalence specification — among the compatible modalities,
    /// which subsets should produce identical Output for the same
    /// inputs? Most workloads return one class containing all
    /// compatible modalities; distinguishability witness workloads
    /// return multiple classes that disagree.
    fn equivalence_classes(&self) -> Vec<Vec<Modality>> {
        vec![self.compatible_modalities().to_vec()]
    }

    /// Observable properties that must hold for every successful run,
    /// independent of which modality executed the workload. Used by
    /// the harness when no cross-modality reference exists (e.g., for
    /// workloads whose `compatible_modalities()` excludes Sequential,
    /// such as `StreamingAggregationWorkload`).
    ///
    /// The `cv` parameter is the `ConfigVector` that drove the run.
    /// Predicates that depend on policy state (e.g., "FIFO invocation
    /// implies strictly-increasing delivery order") read `cv` directly
    /// to decide which invariant to enforce. Predicates that hold
    /// under every `cv` ignore the parameter.
    ///
    /// Each property is a predicate on the workload's `Output`. The
    /// harness asserts every property in the "no reference available"
    /// branch. Returning an empty vector is permitted only
    /// when the workload is in the same equivalence class as the
    /// reference modality (i.e., the dispatcher will always have a
    /// cross-modality reference to compare against).
    ///
    /// Anti-tautology: each property should be non-trivial — it must
    /// constrain the output beyond what `Self::Output: PartialEq` already
    /// guarantees. A property of the form `|_| true` is forbidden.
    fn trace_properties(&self, _cv: &ConfigVector) -> Vec<Box<dyn Fn(&Self::Output) -> bool>> {
        Vec::new()
    }
}

/// Partition invariant (load-bearing — required for dispatcher
/// correctness). Every modality in `compatible_modalities()` must
/// appear in at least one entry of `equivalence_classes()`. The
/// default `equivalence_classes` implementation satisfies this
/// trivially by returning one class containing every compatible
/// modality. Workloads that override `equivalence_classes()` must
/// preserve coverage.
///
/// If this invariant is violated, the dispatcher's `same_class` check
/// silently returns `false` for the dropped modality, falling through
/// to `trace_properties` even when a cross-modality reference should
/// have been available.
pub fn assert_equivalence_classes_cover_compatible<W: Workload>(w: &W) {
    for m in w.compatible_modalities() {
        let covered = w.equivalence_classes().iter().any(|cls| cls.contains(m));
        assert!(
            covered,
            "modality {:?} is compatible but not in any equivalence class",
            m
        );
    }
}

/// Structural validator: every source operator (no incoming edges) is
/// listed in `initial_inputs()`, every operator id used in an edge
/// exists in `operators()`, and (unless StreamGraph is the only
/// compatible modality) the edge set is acyclic.
pub fn assert_workload_well_formed<W: Workload>(w: &W) {
    use std::collections::BTreeSet;
    let ops: Vec<W::OpId> = w.operators().into_iter().map(|(id, _)| id).collect();
    let op_set: BTreeSet<W::OpId> = ops.iter().cloned().collect();
    let edges = w.edges();
    for (from, to) in &edges {
        assert!(
            op_set.contains(from),
            "edge from-id {:?} not declared in operators()",
            from
        );
        assert!(
            op_set.contains(to),
            "edge to-id {:?} not declared in operators()",
            to
        );
    }
    let has_incoming: BTreeSet<W::OpId> = edges.iter().map(|(_, t)| t.clone()).collect();
    let initial = w.initial_inputs();
    for id in &ops {
        let is_source = !has_incoming.contains(id);
        if is_source {
            assert!(
                initial.contains_key(id),
                "source operator {:?} has no initial_inputs entry",
                id
            );
        }
    }
    let only_streamgraph = w.compatible_modalities() == &[Modality::StreamGraph];
    if !only_streamgraph {
        let mut indeg: std::collections::BTreeMap<W::OpId, usize> =
            ops.iter().map(|id| (id.clone(), 0)).collect();
        for (_, t) in &edges {
            *indeg.get_mut(t).expect("to in op_set") += 1;
        }
        let mut frontier: Vec<W::OpId> = indeg
            .iter()
            .filter(|(_, &d)| d == 0)
            .map(|(id, _)| id.clone())
            .collect();
        let mut visited = 0usize;
        while let Some(n) = frontier.pop() {
            visited += 1;
            for (from, to) in &edges {
                if from == &n {
                    let d = indeg.get_mut(to).expect("to in indeg");
                    *d -= 1;
                    if *d == 0 {
                        frontier.push(to.clone());
                    }
                }
            }
        }
        assert!(
            visited == ops.len(),
            "workload graph has a cycle but compatible_modalities is not \
             [StreamGraph]; visited {} of {} ops",
            visited,
            ops.len()
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::workloads::data_pipeline::DataPipelineWorkload;

    #[test]
    fn data_pipeline_equivalence_classes_cover_compatible() {
        let w = DataPipelineWorkload::default_with(6);
        assert_equivalence_classes_cover_compatible(&w);
    }

    #[test]
    fn data_pipeline_is_well_formed() {
        let w = DataPipelineWorkload::default_with(6);
        assert_workload_well_formed(&w);
    }

    #[test]
    fn data_pipeline_declares_all_four_modalities() {
        let w = DataPipelineWorkload::default_with(6);
        let m = w.compatible_modalities();
        assert!(m.contains(&Modality::Sequential));
        assert!(m.contains(&Modality::ForkJoin));
        assert!(m.contains(&Modality::StepGraph));
        assert!(m.contains(&Modality::StreamGraph));
    }
}
