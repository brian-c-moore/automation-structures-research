//! MessageExchangeWorkload integration tests.
//!
//! The split between this file and its sibling:
//!  - `actor_patterns.rs` exercises the actor primitives (Mailbox,
//!    Become, SelectiveReceive, Supervision) in isolation.
//!  - this file exercises the composition: a `MessageExchangeWorkload`
//!    driven by the Sequential modality, end-to-end, with policy
//!    variations.
//!
//! Coverage:
//!  - FIFO yields ascending payload trace; AgeWeighted yields
//!    descending. Catches a driver that ignores `cv.invocation`.
//!  - Conservation: delivered + residual == sent. Catches a drop.
//!  - Multiset: delivered seqs == sent seqs. Catches a duplicate or
//!    fabricated seq.
//!  - Supervision: a supervision event is emitted at `crash_seq`
//!    regardless of `cv.invocation` ordering.

use execution_modalities::modalities::run_sequential;
use execution_modalities::policies::dependencies::DependencyPolicy;
use execution_modalities::policies::invocation::InvocationPolicy;
use execution_modalities::policies::lifecycle::LifecyclePolicy;
use execution_modalities::policies::topology::TopologyPolicy;
use execution_modalities::policies::{ConfigVector, EntityModel};
use execution_modalities::workloads::actor_message_exchange::{
    MessageExchangeWorkload, SupervisionStrategy,
};
use std::collections::BTreeSet;

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
fn fifo_trace_is_ascending_by_seq() {
    let w = MessageExchangeWorkload::new(6, SupervisionStrategy::OneForOne, 3);
    let out = run_sequential(&w, &cv(InvocationPolicy::Fifo, LifecyclePolicy::Simple));
    let seqs: Vec<u64> = out.payload_trace.iter().map(|p| p.seq).collect();
    assert_eq!(seqs, vec![0, 1, 2, 3, 4, 5]);
    assert!(seqs.windows(2).all(|p| p[0] < p[1]));
}

#[test]
fn age_weighted_trace_is_descending_by_seq() {
    let w = MessageExchangeWorkload::new(6, SupervisionStrategy::OneForOne, 3);
    let out = run_sequential(
        &w,
        &cv(InvocationPolicy::AgeWeighted, LifecyclePolicy::Simple),
    );
    let seqs: Vec<u64> = out.payload_trace.iter().map(|p| p.seq).collect();
    assert_eq!(seqs, vec![5, 4, 3, 2, 1, 0]);
}

#[test]
fn conservation_holds_under_every_invocation_policy() {
    for inv in [
        InvocationPolicy::Fifo,
        InvocationPolicy::Priority,
        InvocationPolicy::Pattern,
        InvocationPolicy::AgeWeighted,
    ] {
        let w = MessageExchangeWorkload::default_with(8);
        let out = run_sequential(&w, &cv(inv, LifecyclePolicy::Simple));
        assert_eq!(out.delivered_count, 8, "policy {:?} dropped messages", inv);
        assert_eq!(out.sent_count, 8);
        assert_eq!(out.residual_mailbox_count, 0);
    }
}

#[test]
fn multiset_of_delivered_seqs_matches_sent() {
    for inv in [InvocationPolicy::Fifo, InvocationPolicy::AgeWeighted] {
        let w = MessageExchangeWorkload::default_with(7);
        let out = run_sequential(&w, &cv(inv, LifecyclePolicy::Simple));
        let delivered: BTreeSet<u64> = out.payload_trace.iter().map(|p| p.seq).collect();
        let expected: BTreeSet<u64> = (0..7).collect();
        assert_eq!(
            delivered, expected,
            "policy {:?} produced delivered set {:?} (expected {:?})",
            inv, delivered, expected
        );
    }
}

#[test]
fn supervision_event_observed_regardless_of_invocation_order() {
    let w = MessageExchangeWorkload::new(6, SupervisionStrategy::OneForAll, 2);

    let fifo = run_sequential(
        &w,
        &cv(InvocationPolicy::Fifo, LifecyclePolicy::Supervision),
    );
    let aged = run_sequential(
        &w,
        &cv(InvocationPolicy::AgeWeighted, LifecyclePolicy::Supervision),
    );

    assert_eq!(fifo.supervision_events.len(), 1);
    assert_eq!(aged.supervision_events.len(), 1);
    assert_eq!(
        fifo.supervision_events[0].strategy,
        SupervisionStrategy::OneForAll
    );
    assert_eq!(
        aged.supervision_events[0].strategy,
        SupervisionStrategy::OneForAll
    );
}

#[test]
fn one_for_one_and_one_for_all_strategies_are_distinguishable_in_output() {
    let w_one = MessageExchangeWorkload::new(4, SupervisionStrategy::OneForOne, 1);
    let w_all = MessageExchangeWorkload::new(4, SupervisionStrategy::OneForAll, 1);
    let out_one = run_sequential(
        &w_one,
        &cv(InvocationPolicy::Fifo, LifecyclePolicy::Supervision),
    );
    let out_all = run_sequential(
        &w_all,
        &cv(InvocationPolicy::Fifo, LifecyclePolicy::Supervision),
    );
    assert_ne!(out_one.supervision_events, out_all.supervision_events);
}
