//! Message exchange workload (docs/execution-modalities.md).
//!
//! Reproduces Erlang, Akka, Orleans, Pony. The actor execution model
//! is `(modality = Sequential, entity_model = AddressableEntity,
//! invocation = Message, lifecycle = Supervised)` — one message at a
//! time per handler, runtime-emergent topology over PIDs.
//!
//! The workload encodes a fixed stream of `num_messages` envelopes
//! routed through a single recording handler. The handler's
//! `on_record` records arrival order; at end-of-stream, it emits a
//! single `Summary` record carrying the observed trace and a
//! supervision-event log. `reduce` unpacks the `Summary` into the
//! `MessageExchangeOutput`.
//!
//! `compatible_modalities = &[Sequential]` because mailbox order is
//! observable per-handler, so no cross-modality reference exists. The harness therefore verifies the run via
//! `trace_properties`, which assert message conservation, the
//! multiset of delivered sequence numbers, and policy-conditional
//! FIFO order / supervision-event presence.

use std::collections::{BTreeSet, HashMap};

use crate::modalities::Modality;
use crate::policies::{ConfigVector, InvocationPolicy, LifecyclePolicy};
use crate::workloads::{Operator, OperatorFactory, Workload};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SupervisionStrategy {
    OneForOne,
    OneForAll,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MessageRecord {
    /// An in-flight envelope: a message numbered `seq` from `from` to `to`.
    Envelope { seq: u64, from: u32, to: u32 },
    /// The recording handler's emitted summary at end-of-stream. The
    /// fields mirror `MessageExchangeOutput` so `reduce` can lift them
    /// without re-deriving anything.
    Summary {
        delivered_count: usize,
        sent_count: usize,
        residual_mailbox_count: usize,
        payload_seqs: Vec<u64>,
        supervision_strategies: Vec<SupervisionStrategy>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PayloadTraceEntry {
    pub seq: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SupervisionEvent {
    pub strategy: SupervisionStrategy,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MessageExchangeOutput {
    pub delivered_count: usize,
    pub sent_count: usize,
    pub residual_mailbox_count: usize,
    pub payload_trace: Vec<PayloadTraceEntry>,
    pub supervision_events: Vec<SupervisionEvent>,
}

#[derive(Debug, Clone)]
pub struct MessageExchangeWorkload {
    pub num_messages: u64,
    pub strategy: SupervisionStrategy,
    /// Sequence number at which the recording handler emits a single
    /// supervision event into the trace. Choosing a value in
    /// `0..num_messages` guarantees the event is observed regardless
    /// of `cv.invocation` (FIFO sees `crash_seq` directly; AgeWeighted
    /// sees it after reversing).
    pub crash_seq: u64,
}

impl MessageExchangeWorkload {
    pub fn new(num_messages: u64, strategy: SupervisionStrategy, crash_seq: u64) -> Self {
        assert!(num_messages > 0, "num_messages must be positive");
        assert!(
            crash_seq < num_messages,
            "crash_seq must be a valid envelope index"
        );
        Self {
            num_messages,
            strategy,
            crash_seq,
        }
    }

    pub fn default_with(n: u64) -> Self {
        let crash_seq = n / 2;
        Self::new(n, SupervisionStrategy::OneForOne, crash_seq)
    }

    fn expected_sent_seq_set(&self) -> BTreeSet<u64> {
        (0..self.num_messages).collect()
    }
}

/// Recording handler: consumes envelopes, records their seq in
/// arrival order, and emits a single `Summary` record at EOS.
struct RecorderOp {
    delivered: u64,
    sent_count: u64,
    payload_seqs: Vec<u64>,
    supervision_strategies: Vec<SupervisionStrategy>,
    strategy: SupervisionStrategy,
    crash_seq: u64,
}

impl Operator<MessageRecord> for RecorderOp {
    fn on_record(&mut self, r: MessageRecord) -> Vec<MessageRecord> {
        match r {
            MessageRecord::Envelope { seq, .. } => {
                self.delivered += 1;
                self.payload_seqs.push(seq);
                if seq == self.crash_seq {
                    self.supervision_strategies.push(self.strategy);
                }
            }
            MessageRecord::Summary { .. } => {
                panic!("summary records are outputs and cannot be consumed as input");
            }
        }
        Vec::new()
    }

    fn on_end_of_stream(&mut self) -> Vec<MessageRecord> {
        let delivered = self.delivered as usize;
        let sent = self.sent_count as usize;
        let residual = sent.saturating_sub(delivered);
        vec![MessageRecord::Summary {
            delivered_count: delivered,
            sent_count: sent,
            residual_mailbox_count: residual,
            payload_seqs: std::mem::take(&mut self.payload_seqs),
            supervision_strategies: std::mem::take(&mut self.supervision_strategies),
        }]
    }
}

impl Workload for MessageExchangeWorkload {
    type Record = MessageRecord;
    type Output = MessageExchangeOutput;
    type OpId = &'static str;

    fn operators(&self) -> Vec<(&'static str, OperatorFactory<MessageRecord>)> {
        let strategy = self.strategy;
        let crash_seq = self.crash_seq;
        let sent_count = self.num_messages;
        let factory: OperatorFactory<MessageRecord> = Box::new(move || {
            Box::new(RecorderOp {
                delivered: 0,
                sent_count,
                payload_seqs: Vec::new(),
                supervision_strategies: Vec::new(),
                strategy,
                crash_seq,
            })
        });
        vec![("recorder", factory)]
    }

    fn edges(&self) -> Vec<(&'static str, &'static str)> {
        Vec::new()
    }

    fn initial_inputs(&self) -> HashMap<&'static str, Vec<MessageRecord>> {
        let envelopes: Vec<MessageRecord> = (0..self.num_messages)
            .map(|i| MessageRecord::Envelope {
                seq: i,
                from: 0,
                to: 1,
            })
            .collect();
        let mut m = HashMap::new();
        m.insert("recorder", envelopes);
        m
    }

    fn reduce(
        &self,
        sink_outputs: HashMap<&'static str, Vec<MessageRecord>>,
    ) -> MessageExchangeOutput {
        let mut out = MessageExchangeOutput {
            delivered_count: 0,
            sent_count: 0,
            residual_mailbox_count: 0,
            payload_trace: Vec::new(),
            supervision_events: Vec::new(),
        };
        for (_id, recs) in sink_outputs {
            for r in recs {
                if let MessageRecord::Summary {
                    delivered_count,
                    sent_count,
                    residual_mailbox_count,
                    payload_seqs,
                    supervision_strategies,
                } = r
                {
                    out.delivered_count = delivered_count;
                    out.sent_count = sent_count;
                    out.residual_mailbox_count = residual_mailbox_count;
                    out.payload_trace = payload_seqs
                        .into_iter()
                        .map(|seq| PayloadTraceEntry { seq })
                        .collect();
                    out.supervision_events = supervision_strategies
                        .into_iter()
                        .map(|strategy| SupervisionEvent { strategy })
                        .collect();
                }
            }
        }
        out
    }

    fn compatible_modalities(&self) -> &'static [Modality] {
        &[Modality::Sequential]
    }

    fn trace_properties(
        &self,
        cv: &ConfigVector,
    ) -> Vec<Box<dyn Fn(&MessageExchangeOutput) -> bool>> {
        let mut v: Vec<Box<dyn Fn(&MessageExchangeOutput) -> bool>> = Vec::new();

        // Unconditional: message conservation. Every sent envelope
        // accounts for either a delivery or a residual mailbox
        // occupant. A drop would make delivered + residual < sent.
        v.push(Box::new(|out: &MessageExchangeOutput| {
            out.delivered_count + out.residual_mailbox_count == out.sent_count
        }));

        // Unconditional: every delivered sequence number was sent
        // exactly once. A reorder cannot break this; a drop, a
        // duplicate, or a fabricated seq would.
        let expected_seq_set = self.expected_sent_seq_set();
        v.push(Box::new(move |out: &MessageExchangeOutput| {
            let delivered: BTreeSet<u64> = out.payload_trace.iter().map(|p| p.seq).collect();
            delivered == expected_seq_set
        }));

        // Policy-conditional: under FIFO, delivery order is strictly
        // increasing by seq (insertion order is preserved). Under
        // Priority / Pattern / AgeWeighted, this predicate is not added —
        // those policies are allowed to reorder.
        if cv.invocation == InvocationPolicy::Fifo {
            v.push(Box::new(|out: &MessageExchangeOutput| {
                out.payload_trace.windows(2).all(|p| p[0].seq < p[1].seq)
            }));
        }

        // Policy-conditional: under Supervision, the run recorded at
        // least one supervision event and every event carries a valid
        // strategy. Catches a wiring where the lifecycle axis is
        // declared but no supervision events ever fire.
        if cv.lifecycle == LifecyclePolicy::Supervision {
            v.push(Box::new(|out: &MessageExchangeOutput| {
                !out.supervision_events.is_empty()
                    && out.supervision_events.iter().all(|e| {
                        matches!(
                            e.strategy,
                            SupervisionStrategy::OneForOne | SupervisionStrategy::OneForAll
                        )
                    })
            }));
        }

        v
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::modalities::run_sequential;
    use crate::policies::{
        DependencyPolicy, EntityModel, InvocationPolicy, LifecyclePolicy, TopologyPolicy,
    };

    fn cv(invocation: InvocationPolicy, lifecycle: LifecyclePolicy) -> ConfigVector {
        ConfigVector {
            invocation,
            entity_model: EntityModel::AddressableEntity,
            topology: TopologyPolicy::RuntimeAddressable,
            dependencies: DependencyPolicy::Fixed,
            lifecycle,
        }
    }

    #[test]
    fn fifo_preserves_insertion_order() {
        let w = MessageExchangeWorkload::default_with(5);
        let out = run_sequential(&w, &cv(InvocationPolicy::Fifo, LifecyclePolicy::Simple));
        let seqs: Vec<u64> = out.payload_trace.iter().map(|p| p.seq).collect();
        assert_eq!(seqs, vec![0, 1, 2, 3, 4]);
    }

    #[test]
    fn age_weighted_reverses_insertion_order() {
        let w = MessageExchangeWorkload::default_with(5);
        let out = run_sequential(
            &w,
            &cv(InvocationPolicy::AgeWeighted, LifecyclePolicy::Simple),
        );
        let seqs: Vec<u64> = out.payload_trace.iter().map(|p| p.seq).collect();
        assert_eq!(seqs, vec![4, 3, 2, 1, 0]);
    }

    #[test]
    fn supervision_event_is_recorded_at_crash_seq() {
        let w = MessageExchangeWorkload::new(6, SupervisionStrategy::OneForAll, 3);
        let out = run_sequential(
            &w,
            &cv(InvocationPolicy::Fifo, LifecyclePolicy::Supervision),
        );
        assert_eq!(out.supervision_events.len(), 1);
        assert_eq!(
            out.supervision_events[0].strategy,
            SupervisionStrategy::OneForAll
        );
    }

    #[test]
    fn conservation_holds_no_drops() {
        let w = MessageExchangeWorkload::default_with(7);
        let out = run_sequential(&w, &cv(InvocationPolicy::Fifo, LifecyclePolicy::Simple));
        assert_eq!(out.delivered_count, 7);
        assert_eq!(out.sent_count, 7);
        assert_eq!(out.residual_mailbox_count, 0);
    }

    #[test]
    fn conservation_property_rejects_overdelivery() {
        let w = MessageExchangeWorkload::default_with(4);
        let forged = MessageExchangeOutput {
            delivered_count: 5,
            sent_count: 4,
            residual_mailbox_count: 1,
            payload_trace: (0..4).map(|seq| PayloadTraceEntry { seq }).collect(),
            supervision_events: Vec::new(),
        };
        let properties = w.trace_properties(&cv(InvocationPolicy::Fifo, LifecyclePolicy::Simple));
        assert!(!properties.iter().all(|property| property(&forged)));
    }

    #[test]
    #[should_panic(expected = "summary records are outputs")]
    fn recorder_rejects_summary_as_input() {
        let mut recorder = RecorderOp {
            delivered: 0,
            sent_count: 1,
            payload_seqs: Vec::new(),
            supervision_strategies: Vec::new(),
            strategy: SupervisionStrategy::OneForOne,
            crash_seq: 0,
        };
        recorder.on_record(MessageRecord::Summary {
            delivered_count: 0,
            sent_count: 0,
            residual_mailbox_count: 0,
            payload_seqs: Vec::new(),
            supervision_strategies: Vec::new(),
        });
    }
}
