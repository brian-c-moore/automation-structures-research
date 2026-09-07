//! Fork-join modality (docs/execution-modalities.md).
//!
//! Partition the source records across N OS-thread workers. Each
//! worker drives the workload's operator graph end-to-end over its
//! own chunk; outputs are barrier-joined and routed to `reduce`.
//!
//! Uses `thread::scope` so worker threads can borrow `&W` without
//! requiring `W::OpId: Sync` on the trait. Per-thread, each worker
//! materializes its own copy of the operator factories from `&W`,
//! then runs a chunk-sized topological execution.

use crate::policies::ConfigVector;
use crate::workloads::{Operator, OperatorFactory, Workload};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::thread;

const DEFAULT_NUM_WORKERS: usize = 4;

/// Run the workload through fork-join with the default worker count.
/// Used by the harness dispatcher.
///
/// The policy axes map as follows for fork-join:
///   - invocation: partition assignment (FIFO = sequential chunks;
///     AgeWeighted = reverse-order chunks). Implemented by reordering
///     each source-operator's record list before chunking.
///   - entity_model, topology, dependencies, and lifecycle: not
///     interpreted. The driver uses index chunks, declared workload
///     edges, per-worker fixed factories, and a scoped-thread barrier.
pub fn run_fork_join<W: Workload>(workload: &W, cv: &ConfigVector) -> W::Output
where
    W::OpId: Ord,
{
    run_fork_join_with_workers(workload, cv, DEFAULT_NUM_WORKERS)
}

/// Explicit-worker-count entry; used by tests that vary worker count.
pub fn run_fork_join_with_workers<W: Workload>(
    workload: &W,
    cv: &ConfigVector,
    num_workers: usize,
) -> W::Output
where
    W::OpId: Ord,
{
    assert!(num_workers > 0, "num_workers must be positive");
    let edges = workload.edges();
    let initial = workload.initial_inputs();

    let mut succs: BTreeMap<W::OpId, Vec<W::OpId>> = BTreeMap::new();
    for (from, to) in &edges {
        succs.entry(from.clone()).or_default().push(to.clone());
    }
    let topo: Vec<W::OpId> = {
        let ops = workload.operators();
        topological_order::<W>(&ops, &edges)
            .expect("fork-join driver requires acyclic workload graph")
    };
    let sink_set: BTreeSet<W::OpId> = topo
        .iter()
        .filter(|id| succs.get(*id).map(|s| s.is_empty()).unwrap_or(true))
        .cloned()
        .collect();

    // Partition initial records by source-operator id. Fork-join's
    // "invocation = partition assignment" is implemented by reordering
    // each source-operator's record list (FIFO = unchanged;
    // AgeWeighted = reversed) before chunking. The resulting chunks are
    // then handed to workers in BTreeMap order.
    let initial: BTreeMap<W::OpId, Vec<W::Record>> = initial
        .into_iter()
        .map(|(id, recs)| (id, cv.invocation.reorder_batch(recs, |_| 0i64)))
        .collect();
    let total_records: usize = initial.values().map(|v| v.len()).sum();
    let workers = num_workers.min(total_records.max(1));
    let chunk_size = (total_records + workers - 1) / workers.max(1);

    let mut chunks: Vec<BTreeMap<W::OpId, Vec<W::Record>>> =
        (0..workers).map(|_| BTreeMap::new()).collect();
    {
        let mut emitted = 0usize;
        for (id, recs) in &initial {
            for r in recs {
                let target = (emitted / chunk_size.max(1)).min(workers - 1);
                chunks[target]
                    .entry(id.clone())
                    .or_default()
                    .push(r.clone());
                emitted += 1;
            }
        }
    }

    let combined: HashMap<W::OpId, Vec<W::Record>> = thread::scope(|s| {
        let mut handles = Vec::with_capacity(workers);
        for chunk in chunks {
            // Clone the structural data per worker so the trait does
            // not need to require `OpId: Sync`; the trait bound is only
            // `Send + 'static`.
            let local_topo = topo.clone();
            let local_succs = succs.clone();
            let local_sink = sink_set.clone();
            handles.push(s.spawn(move || {
                let local_ops = workload.operators();
                let local_factories: BTreeMap<W::OpId, OperatorFactory<W::Record>> =
                    local_ops.into_iter().collect();
                run_chunk::<W>(
                    chunk,
                    &local_factories,
                    &local_topo,
                    &local_succs,
                    &local_sink,
                )
            }));
        }

        let mut merged: HashMap<W::OpId, Vec<W::Record>> = HashMap::new();
        for h in handles {
            let part = h.join().expect("fork-join worker panicked");
            for (id, recs) in part {
                merged.entry(id).or_default().extend(recs);
            }
        }
        merged
    });

    workload.reduce(combined)
}

fn run_chunk<W: Workload>(
    initial: BTreeMap<W::OpId, Vec<W::Record>>,
    factories: &BTreeMap<W::OpId, OperatorFactory<W::Record>>,
    topo: &[W::OpId],
    succs: &BTreeMap<W::OpId, Vec<W::OpId>>,
    sink_set: &BTreeSet<W::OpId>,
) -> HashMap<W::OpId, Vec<W::Record>>
where
    W::OpId: Ord,
{
    let mut buffers: BTreeMap<W::OpId, Vec<W::Record>> = initial;
    let mut sink_out: HashMap<W::OpId, Vec<W::Record>> = HashMap::new();
    for id in topo {
        let factory = factories.get(id).expect("factory exists");
        let mut op: Box<dyn Operator<W::Record>> = factory();
        let inputs = buffers.remove(id).unwrap_or_default();
        let mut produced: Vec<W::Record> = Vec::new();
        for r in inputs {
            produced.extend(op.on_record(r));
        }
        produced.extend(op.on_end_of_stream());

        if sink_set.contains(id) {
            sink_out.entry(id.clone()).or_default().extend(produced);
        } else {
            let downstream = succs.get(id).cloned().unwrap_or_default();
            for d in downstream {
                buffers
                    .entry(d)
                    .or_default()
                    .extend(produced.iter().cloned());
            }
        }
    }
    sink_out
}

fn topological_order<W: Workload>(
    operators: &[(W::OpId, OperatorFactory<W::Record>)],
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
