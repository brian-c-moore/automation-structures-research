//! Sequential modality (docs/execution-modalities.md).
//!
//! Topological order over the workload's operator graph; each operator
//! drains its accumulated input buffer end-to-end before its successor
//! becomes eligible. One operator runs at a time; within an operator,
//! one record is handled at a time.

use crate::policies::ConfigVector;
use crate::workloads::Workload;
use std::collections::{BTreeMap, HashMap};

/// Sequential modality driver. It consults `cv.invocation` to reorder
/// each operator's input buffer before draining (`cv.invocation = FIFO`
/// keeps insertion order; `AgeWeighted` reverses; Priority/Pattern
/// require richer record metadata than this generic driver can extract
/// and are identity reorderings here, refined per-workload).
///
/// `cv.entity_model`, `cv.topology`, `cv.dependencies`, and
/// `cv.lifecycle` are not interpreted by this generic driver. Its
/// semantics are fixed: one thread, one operator at a time, declared
/// workload edges, fixed factories, and one invocation lifetime.
pub fn run_sequential<W: Workload>(workload: &W, cv: &ConfigVector) -> W::Output
where
    W::OpId: Ord,
{
    let operators = workload.operators();
    let edges = workload.edges();
    let initial = workload.initial_inputs();

    let mut preds: BTreeMap<W::OpId, Vec<W::OpId>> = BTreeMap::new();
    let mut succs: BTreeMap<W::OpId, Vec<W::OpId>> = BTreeMap::new();
    for (from, to) in &edges {
        preds.entry(to.clone()).or_default().push(from.clone());
        succs.entry(from.clone()).or_default().push(to.clone());
    }

    let mut topo_order = topological_order::<W>(&operators, &edges)
        .expect("sequential driver requires acyclic workload graph");

    let mut buffers: BTreeMap<W::OpId, Vec<W::Record>> = BTreeMap::new();
    for (id, init) in initial.into_iter() {
        buffers.insert(id, init);
    }

    let factories: BTreeMap<W::OpId, _> = operators.into_iter().collect();

    for id in topo_order.drain(..) {
        let factory = factories.get(&id).expect("factory exists");
        let mut op = factory();
        let inputs = buffers.remove(&id).unwrap_or_default();
        // Reorder inputs per cv.invocation. The index_of extractor is
        // a constant 0 here because a generic W::Record carries no score;
        // FIFO and AgeWeighted only need the position
        // information that reorder_batch already has from Vec order.
        let inputs = cv.invocation.reorder_batch(inputs, |_| 0i64);
        let mut produced: Vec<W::Record> = Vec::new();
        for r in inputs {
            produced.extend(op.on_record(r));
        }
        produced.extend(op.on_end_of_stream());

        let downstream = succs.get(&id).cloned().unwrap_or_default();
        if downstream.is_empty() {
            buffers.insert(id, produced);
        } else {
            for d in downstream {
                buffers
                    .entry(d)
                    .or_default()
                    .extend(produced.iter().cloned());
            }
        }
    }

    let sinks: HashMap<W::OpId, Vec<W::Record>> = factories
        .keys()
        .filter(|id| succs.get(id).map(|s| s.is_empty()).unwrap_or(true))
        .filter_map(|id| buffers.remove(id).map(|out| (id.clone(), out)))
        .collect();

    workload.reduce(sinks)
}

fn topological_order<W: Workload>(
    operators: &[(W::OpId, crate::workloads::OperatorFactory<W::Record>)],
    edges: &[(W::OpId, W::OpId)],
) -> Result<Vec<W::OpId>, ()> {
    let mut indeg: BTreeMap<W::OpId, usize> =
        operators.iter().map(|(id, _)| (id.clone(), 0)).collect();
    for (_, to) in edges {
        if let Some(d) = indeg.get_mut(to) {
            *d += 1;
        }
    }
    let mut ready: Vec<W::OpId> = indeg
        .iter()
        .filter(|(_, &d)| d == 0)
        .map(|(id, _)| id.clone())
        .collect();
    let mut order: Vec<W::OpId> = Vec::with_capacity(operators.len());
    while let Some(n) = ready.pop() {
        order.push(n.clone());
        for (from, to) in edges {
            if from == &n {
                if let Some(d) = indeg.get_mut(to) {
                    *d -= 1;
                    if *d == 0 {
                        ready.push(to.clone());
                    }
                }
            }
        }
    }
    if order.len() == operators.len() {
        Ok(order)
    } else {
        Err(())
    }
}
