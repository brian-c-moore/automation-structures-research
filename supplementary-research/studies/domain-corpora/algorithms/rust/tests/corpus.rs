//! Corpus test entrypoints. Each phase test asserts operational
//! equivalence (no divergence) for its algorithms; `full_report`
//! records the whole corpus and writes `results.md`.

use dac_algorithms::harness;

fn assert_phase(phase: u8) {
    let outcomes = harness::run(Some(phase));
    assert!(
        !outcomes.is_empty(),
        "phase {phase} has no registered algorithms"
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
fn phase1_dp() {
    assert_phase(1);
}

#[test]
fn phase2_stack_bsearch() {
    assert_phase(2);
}

#[test]
fn phase3_adv_graphs() {
    assert_phase(3);
}

#[test]
fn phase4_backtracking() {
    assert_phase(4);
}

#[test]
fn phase5_trees_heap() {
    assert_phase(5);
}

#[test]
fn phase6_arrays() {
    assert_phase(6);
}

#[test]
fn phase7_lists_tries_graphs() {
    assert_phase(7);
}

#[test]
fn phase8_greedy_intervals_math_bit() {
    assert_phase(8);
}

/// Runs every registered algorithm, writes the manifest and results.md.
/// Does not assert (records the corpus state); the per-phase tests are
/// the pass/fail gate.
#[test]
fn full_report() {
    let _ = dac_algorithms::config::write_manifest();
    let outcomes = harness::run(None);
    let body = harness::report(&outcomes);
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/results.md");
    let header = "# Algorithms corpus — run results (auto-generated)\n\n\
        Per-algorithm results from the last `cargo test --no-fail-fast`\n\
        run.\n\n";
    std::fs::write(path, format!("{header}{body}")).unwrap();
    eprintln!("{body}");
}
