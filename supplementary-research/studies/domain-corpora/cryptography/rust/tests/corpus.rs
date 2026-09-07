//! Executable-subset comparisons against the exact Python oracles.
//! The KAT-vector tests live in `kat_tests.rs`.
//!
//! Groups 1, 2, 4, and 5 contain the seven implemented algorithms.
//! No empty group is treated as success.

use dac_cryptography::harness;

fn assert_phase(phase: u8) {
    let outcomes = harness::run(Some(phase));
    assert!(
        !outcomes.is_empty(),
        "group {phase} has no registered algorithms"
    );
    let mut failures = Vec::new();
    for o in &outcomes {
        eprintln!(
            "phase {} {:<32} {}/{}  [{}]",
            o.phase, o.name, o.passed, o.total, o.ordering
        );
        if !o.ok() {
            for d in &o.divergences {
                eprintln!(
                    "  DIVERGENCE {}: input={:?} got={:?} want={:?}",
                    o.name, d.input, d.got, d.want
                );
            }
            failures.push(o.name);
        }
    }
    assert!(
        failures.is_empty(),
        "divergences in phase {phase}: {failures:?}"
    );
}

#[test]
fn phase1_hashes() {
    assert_phase(1);
}
#[test]
fn phase2_symmetric() {
    assert_phase(2);
}
#[test]
fn phase4_mac() {
    assert_phase(4);
}
#[test]
fn phase5_kdf() {
    assert_phase(5);
}

/// Runs every registered algorithm and requires all seven exact entries.
#[test]
fn full_corpus() {
    let outcomes = harness::run(None);
    assert_eq!(
        outcomes.len(),
        7,
        "registry must contain the exact seven-algorithm subset"
    );
    let failures: Vec<_> = outcomes.iter().filter(|outcome| !outcome.ok()).collect();
    assert!(failures.is_empty(), "full-corpus divergences: {failures:?}");
}
