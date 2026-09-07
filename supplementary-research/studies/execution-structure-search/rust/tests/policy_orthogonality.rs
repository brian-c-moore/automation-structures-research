//! Selected policy-mechanism tests.
//!
//! These tests cover one local invariant per policy module and show
//! that FIFO versus AgeWeighted invocation is observable in the
//! Sequential driver. They do not establish arbitrary-axis
//! orthogonality or product-policy fidelity.

use execution_modalities::modalities::run_sequential;
use execution_modalities::policies::dependencies::{BehaviorSlot, DependencyPolicy};
use execution_modalities::policies::invocation::{InvocationPolicy, Item};
use execution_modalities::policies::lifecycle::{LifecyclePolicy, WorkerLifecycle};
use execution_modalities::policies::topology::{TopologyPolicy, TopologyState};
use execution_modalities::policies::{ConfigVector, EntityModel};
use execution_modalities::primitives::queue::BoundedQueue;
use execution_modalities::workloads::actor_message_exchange::{
    MessageExchangeWorkload, SupervisionStrategy,
};
use std::collections::BTreeSet;

#[test]
fn invocation_policies_each_choose_a_valid_index() {
    let items = [
        Item {
            value: 1,
            priority: 5,
            matches_pattern: false,
            age: 1,
        },
        Item {
            value: 2,
            priority: 1,
            matches_pattern: true,
            age: 9,
        },
        Item {
            value: 3,
            priority: 3,
            matches_pattern: false,
            age: 5,
        },
    ];
    let mut q = BoundedQueue::new(3);
    for it in &items {
        q.enqueue(*it).unwrap();
    }

    for policy in [
        InvocationPolicy::Fifo,
        InvocationPolicy::Priority,
        InvocationPolicy::Pattern,
        InvocationPolicy::AgeWeighted,
    ] {
        let chosen = policy.choose(&q);
        assert!(chosen.is_some(), "policy {:?} returned None", policy);
        assert!(chosen.unwrap() < q.len());
    }
}

#[test]
fn topology_policies_respect_their_invariants() {
    let allowed: BTreeSet<(String, String)> = [
        ("a".to_string(), "b".to_string()),
        ("b".to_string(), "c".to_string()),
    ]
    .into_iter()
    .collect();

    for policy in [
        TopologyPolicy::DeclaredStatic,
        TopologyPolicy::DeclaredMutable,
        TopologyPolicy::RuntimeAddressable,
        TopologyPolicy::RuntimeAnonymous,
    ] {
        let mut t = TopologyState::new(allowed.clone(), policy);
        // Try every kind of mutation; whichever the policy allows
        // should leave the bounded invariant intact.
        t.try_swap(("a".into(), "b".into()), policy);
        t.try_learn_ref("a".into(), "b".into(), policy);
        t.try_add_anonymous(("b".into(), "c".into()), policy);
        assert!(t.check_bounded());
        assert!(t.check_addressable_consistency(policy));
    }
}

#[test]
fn dependency_policies_respect_fixed_invariant() {
    let initial: Box<dyn Fn(i64) -> i64 + Send + Sync> = Box::new(|x| x + 1);
    let mut slot = BehaviorSlot::new(initial, DependencyPolicy::Fixed);
    let new_fn: Box<dyn Fn(i64) -> i64 + Send + Sync> = Box::new(|x| x * 2);
    let swapped = slot.try_become(new_fn);
    assert!(!swapped);
    assert!(slot.check_fixed_no_change());
    assert_eq!(slot.invoke(3), 4);
}

#[test]
fn lifecycle_policies_respect_simple_invariant() {
    let mut wl = WorkerLifecycle::new(LifecyclePolicy::Simple, 0);
    wl.spawn();
    wl.crash();
    let restarted = wl.supervised_restart();
    assert!(!restarted);
    assert!(wl.check_simple_no_restart());
}

// ----- Invocation anti-tautology integration check -----
//
// This check requires the Sequential driver to read `cv.invocation`
// and reflect it in observable output. If it ignores that field, the
// FIFO-vs-AgeWeighted-with-same-input run produces identical output,
// which would silently nullify this bounded policy mechanism. This test
// runs `MessageExchangeWorkload` (the actor-mailbox handler whose
// payload trace records arrival order) under both policies through
// Sequential and asserts the emitted traces differ.
//
// The test uses the public `MessageExchangeWorkload` defined in
// `workloads::actor_message_exchange`.

fn cv_with_invocation(policy: InvocationPolicy) -> ConfigVector {
    ConfigVector {
        invocation: policy,
        entity_model: EntityModel::AddressableEntity,
        topology: TopologyPolicy::RuntimeAddressable,
        dependencies: DependencyPolicy::Fixed,
        lifecycle: LifecyclePolicy::Simple,
    }
}

#[test]
fn invocation_axis_is_observable_in_sequential_output() {
    let w = MessageExchangeWorkload::new(5, SupervisionStrategy::OneForOne, 2);
    let fifo = run_sequential(&w, &cv_with_invocation(InvocationPolicy::Fifo));
    let aged = run_sequential(&w, &cv_with_invocation(InvocationPolicy::AgeWeighted));

    let fifo_seqs: Vec<u64> = fifo.payload_trace.iter().map(|p| p.seq).collect();
    let aged_seqs: Vec<u64> = aged.payload_trace.iter().map(|p| p.seq).collect();

    // Expected: FIFO preserves insertion order [0,1,2,3,4];
    // AgeWeighted reverses to [4,3,2,1,0]. If the driver is not
    // reading cv.invocation, both runs produce the same trace and
    // these assertions fail.
    assert_eq!(
        fifo_seqs,
        vec![0, 1, 2, 3, 4],
        "FIFO drained out of insertion order: {:?}",
        fifo_seqs
    );
    assert_eq!(
        aged_seqs,
        vec![4, 3, 2, 1, 0],
        "AgeWeighted did not reverse insertion order: {:?}",
        aged_seqs
    );
    assert_ne!(
        fifo_seqs, aged_seqs,
        "invocation axis is wired but not observable: \
         FIFO and AgeWeighted produced identical traces {:?}",
        fifo_seqs
    );

    // The multiset of delivered seqs is identical across policies —
    // reordering must not lose or fabricate messages.
    let fifo_set: BTreeSet<u64> = fifo_seqs.iter().copied().collect();
    let aged_set: BTreeSet<u64> = aged_seqs.iter().copied().collect();
    assert_eq!(
        fifo_set, aged_set,
        "policy axis reordering must preserve the delivered multiset"
    );
}
