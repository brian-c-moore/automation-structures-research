//! Streaming graph modality (docs/execution-modalities.md).
//!
//! This finite acyclic driver interleaves operators against bounded
//! queues on each edge. It iterates a "make progress" loop until source
//! records are drained, all queues are empty, and every operator has
//! emitted its end-of-stream output.

use crate::policies::ConfigVector;
use crate::primitives::queue::BoundedQueue;
use crate::workloads::{Operator, Workload};
use std::collections::{BTreeMap, HashMap, VecDeque};

const DEFAULT_QUEUE_CAPACITY: usize = 2;

struct PendingBatch<R> {
    records: VecDeque<R>,
    completes_eos: bool,
}

/// Run the workload through stream-graph with the default queue
/// capacity. Used by the harness dispatcher.
///
/// The policy axes map as follows:
///   - invocation: per-edge queue consumption order at fan-in points.
///     The current driver consumes predecessor edges in BTreeMap
///     iteration order (deterministic); with `cv.invocation =
///     AgeWeighted`, that iteration is reversed so the most-recently
///     declared predecessor edge is drained first. FIFO keeps the
///     ascending OpId order.
///   - entity_model, topology, dependencies, and lifecycle: not
///     interpreted. Endpoint identity is `OpId`, topology comes from
///     `workload.edges()`, factories are fixed, and this finite driver
///     performs no crash injection or recovery.
pub fn run_stream_graph<W: Workload>(workload: &W, cv: &ConfigVector) -> W::Output
where
    W::OpId: Ord,
{
    run_stream_graph_with_capacity(workload, cv, DEFAULT_QUEUE_CAPACITY)
}

/// Explicit-capacity entry; used by tests that vary edge capacity.
pub fn run_stream_graph_with_capacity<W: Workload>(
    workload: &W,
    cv: &ConfigVector,
    capacity: usize,
) -> W::Output
where
    W::OpId: Ord,
{
    assert!(capacity > 0, "queue capacity must be positive");
    let operators = workload.operators();
    let edges = workload.edges();
    let initial = workload.initial_inputs();

    let mut preds: BTreeMap<W::OpId, Vec<W::OpId>> = BTreeMap::new();
    let mut succs: BTreeMap<W::OpId, Vec<W::OpId>> = BTreeMap::new();
    for (from, to) in &edges {
        preds.entry(to.clone()).or_default().push(from.clone());
        succs.entry(from.clone()).or_default().push(to.clone());
    }

    // Per-edge queue keyed by (from, to). Per-operator instance + EOS
    // flag + an inbox queue (the merged predecessor records waiting to
    // be consumed by this operator).
    let mut edge_queues: BTreeMap<(W::OpId, W::OpId), BoundedQueue<W::Record>> = edges
        .iter()
        .map(|e| (e.clone(), BoundedQueue::new(capacity)))
        .collect();

    let mut instances: BTreeMap<W::OpId, Box<dyn Operator<W::Record>>> = BTreeMap::new();
    for (id, factory) in &operators {
        instances.insert(id.clone(), factory());
    }

    // Sources' initial input queues are an internal staging buffer
    // (not bounded by `capacity`, since they represent the workload's
    // declared input list — the moral equivalent of an external
    // source feeding the operator one record at a time).
    let mut source_input: BTreeMap<W::OpId, std::collections::VecDeque<W::Record>> =
        BTreeMap::new();
    for (id, recs) in initial.into_iter() {
        source_input.insert(id, recs.into_iter().collect());
    }
    // Sink output buffers.
    let mut sink_out: HashMap<W::OpId, Vec<W::Record>> = HashMap::new();
    let op_ids: Vec<W::OpId> = operators.iter().map(|(id, _)| id.clone()).collect();

    // `eos_completed[id]` becomes true after the operator has
    // received EOS and `on_end_of_stream` has been called.
    let mut eos_completed: BTreeMap<W::OpId, bool> =
        op_ids.iter().map(|id| (id.clone(), false)).collect();
    // An operator is never invoked again while it has undelivered
    // output. Records are drained one at a time so a batch larger
    // than an edge's capacity still makes bounded progress.
    let mut pending: BTreeMap<W::OpId, PendingBatch<W::Record>> = BTreeMap::new();

    loop {
        let mut progressed = false;

        for id in &op_ids {
            if let Some(batch) = pending.get_mut(id) {
                if let Some(record) = batch.records.front() {
                    if deposit_one::<W>(id, record, &succs, &mut edge_queues, &mut sink_out) {
                        batch.records.pop_front();
                        progressed = true;
                    }
                }

                if batch.records.is_empty() {
                    let completes_eos = batch.completes_eos;
                    pending.remove(id);
                    if completes_eos {
                        eos_completed.insert(id.clone(), true);
                    }
                    progressed = true;
                }
                // Preserve the one-step discipline: after delivering
                // pending output, reconsider this operator on the next
                // scheduler pass.
                continue;
            }

            // Source operators: emit one record from their staging
            // queue if successors have room (or there are no
            // successors, in which case they accumulate at the sink).
            let is_source = preds.get(id).map(|p| p.is_empty()).unwrap_or(true);

            if is_source {
                if let Some(buf) = source_input.get_mut(id) {
                    if let Some(r) = buf.pop_front() {
                        let op = instances.get_mut(id).expect("op exists");
                        let produced = op.on_record(r);
                        pending.insert(
                            id.clone(),
                            PendingBatch {
                                records: produced.into(),
                                completes_eos: false,
                            },
                        );
                        progressed = true;
                    } else if !eos_completed.get(id).copied().unwrap_or(false) {
                        // Source's input is drained; signal EOS through
                        // the operator.
                        let op = instances.get_mut(id).expect("op exists");
                        let flushed = op.on_end_of_stream();
                        pending.insert(
                            id.clone(),
                            PendingBatch {
                                records: flushed.into(),
                                completes_eos: true,
                            },
                        );
                        progressed = true;
                    }
                }
                continue;
            }

            // Non-source operators: consume one record from any
            // predecessor edge with data and emit produced records to
            // successors. cv.invocation reorders the predecessor list
            // for fan-in disambiguation (FIFO = ascending OpId,
            // AgeWeighted = reversed).
            let mut consumed_one = false;
            let p_list = preds.get(id).cloned().unwrap_or_default();
            let p_list = cv.invocation.reorder_batch(p_list, |_| 0i64);
            for p in &p_list {
                let key = (p.clone(), id.clone());
                if let Some(q) = edge_queues.get_mut(&key) {
                    if !q.is_empty() {
                        let r = q.dequeue().expect("non-empty");
                        let op = instances.get_mut(id).expect("op exists");
                        let produced = op.on_record(r);
                        pending.insert(
                            id.clone(),
                            PendingBatch {
                                records: produced.into(),
                                completes_eos: false,
                            },
                        );
                        consumed_one = true;
                        progressed = true;
                        break;
                    }
                }
            }
            if consumed_one {
                continue;
            }

            // No record available, all predecessor EOS reached? Then
            // call on_end_of_stream and mark this op completed.
            let all_preds_eos = p_list
                .iter()
                .all(|p| eos_completed.get(p).copied().unwrap_or(false));
            let preds_empty = p_list.iter().all(|p| {
                edge_queues
                    .get(&(p.clone(), id.clone()))
                    .map(|q| q.is_empty())
                    .unwrap_or(true)
            });
            if all_preds_eos && preds_empty && !eos_completed.get(id).copied().unwrap_or(false) {
                let op = instances.get_mut(id).expect("op exists");
                let flushed = op.on_end_of_stream();
                pending.insert(
                    id.clone(),
                    PendingBatch {
                        records: flushed.into(),
                        completes_eos: true,
                    },
                );
                progressed = true;
            }
        }

        if !progressed {
            let unfinished = !pending.is_empty()
                || source_input.values().any(|queue| !queue.is_empty())
                || edge_queues.values().any(|queue| !queue.is_empty())
                || eos_completed.values().any(|complete| !complete);
            assert!(
                !unfinished,
                "stream-graph driver stalled before every bounded input and EOS record was delivered"
            );
            break;
        }
    }

    workload.reduce(sink_out)
}

/// Deposit one record onto every successor edge of `id`. If any
/// downstream queue is full, return false without modifying state.
/// Fan-out is therefore atomic even under bounded backpressure.
fn deposit_one<W: Workload>(
    id: &W::OpId,
    record: &W::Record,
    succs: &BTreeMap<W::OpId, Vec<W::OpId>>,
    edge_queues: &mut BTreeMap<(W::OpId, W::OpId), BoundedQueue<W::Record>>,
    sink_out: &mut HashMap<W::OpId, Vec<W::Record>>,
) -> bool
where
    W::OpId: Ord,
{
    let downstream = succs.get(id).cloned().unwrap_or_default();
    if downstream.is_empty() {
        sink_out.entry(id.clone()).or_default().push(record.clone());
        return true;
    }
    for d in &downstream {
        let key = (id.clone(), d.clone());
        if let Some(q) = edge_queues.get(&key) {
            if q.len() == q.capacity() {
                return false;
            }
        }
    }
    for d in &downstream {
        let key = (id.clone(), d.clone());
        let q = edge_queues.get_mut(&key).expect("edge queue exists");
        q.enqueue(record.clone()).expect("capacity pre-checked");
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::modalities::Modality;
    use crate::workloads::OperatorFactory;

    struct BurstSource;

    impl Operator<i64> for BurstSource {
        fn on_record(&mut self, _record: i64) -> Vec<i64> {
            vec![10, 11, 12]
        }

        fn on_end_of_stream(&mut self) -> Vec<i64> {
            vec![20, 21, 22]
        }
    }

    struct Pass;

    impl Operator<i64> for Pass {
        fn on_record(&mut self, record: i64) -> Vec<i64> {
            vec![record]
        }
    }

    struct BurstWorkload;

    impl Workload for BurstWorkload {
        type Record = i64;
        type Output = Vec<i64>;
        type OpId = &'static str;

        fn operators(&self) -> Vec<(Self::OpId, OperatorFactory<Self::Record>)> {
            vec![
                ("source", Box::new(|| Box::new(BurstSource))),
                ("sink", Box::new(|| Box::new(Pass))),
            ]
        }

        fn edges(&self) -> Vec<(Self::OpId, Self::OpId)> {
            vec![("source", "sink")]
        }

        fn initial_inputs(&self) -> HashMap<Self::OpId, Vec<Self::Record>> {
            HashMap::from([("source", vec![1])])
        }

        fn reduce(&self, mut sink_outputs: HashMap<Self::OpId, Vec<Self::Record>>) -> Self::Output {
            sink_outputs.remove("sink").unwrap_or_default()
        }

        fn compatible_modalities(&self) -> &'static [Modality] {
            &[Modality::StreamGraph]
        }
    }

    #[test]
    fn backpressure_preserves_record_and_eos_batches_larger_than_capacity() {
        let output =
            run_stream_graph_with_capacity(&BurstWorkload, &ConfigVector::default_for_test(), 1);
        assert_eq!(output, vec![10, 11, 12, 20, 21, 22]);
    }
}
