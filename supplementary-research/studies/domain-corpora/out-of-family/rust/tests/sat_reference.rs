//! Reference validation for **the DPLL procedure**.
//!
//! * **Literature anchor.** The pigeonhole family: `n+1` pigeons into
//!   `n` holes is the standard unsatisfiable benchmark, and `n` into `n`
//!   is satisfiable. Verdicts are fixed by the principle, not by this
//!   implementation.
//! * **Second oracle.** Every satisfiable verdict is checked by an
//!   independent model checker, and both verdicts are cross-checked
//!   against exhaustive enumeration over all assignments — a different
//!   method computing the same predicate — on a deterministic batch of
//!   random 3-CNF formulas spanning the satisfiable/unsatisfiable
//!   threshold.

use dac_out_of_family::{pigeonhole, Clause, Cnf, Lit, SatOutcome};

const BUDGET: usize = 5_000_000;

fn solve(cnf: &Cnf) -> SatOutcome {
    dac_out_of_family::solve(cnf, BUDGET)
}

// --- literature anchor -----------------------------------------------

#[test]
fn the_pigeonhole_principle_holds_at_every_size_checked() {
    for holes in 1..=4 {
        // n+1 pigeons into n holes: unsatisfiable.
        let over = pigeonhole(holes + 1, holes);
        assert_eq!(
            solve(&over),
            SatOutcome::Unsat,
            "{} pigeons into {holes} holes should be unsatisfiable",
            holes + 1
        );
        // n pigeons into n holes: satisfiable, and the model must check.
        let exact = pigeonhole(holes, holes);
        match solve(&exact) {
            SatOutcome::Sat(m) => assert!(
                exact.satisfied_by(&m),
                "returned model does not satisfy {holes} into {holes}"
            ),
            other => panic!("{holes} into {holes} should be Sat, got {other:?}"),
        }
    }
}

// --- second oracle: exhaustive enumeration ---------------------------

/// Deterministic 3-CNF generator: a linear congruential stream, so the
/// batch is fixed and reproducible.
fn random_3cnf(seed: u64, nvars: usize, nclauses: usize) -> Cnf {
    let mut state = seed;
    let mut next = || {
        state = state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        (state >> 33) as usize
    };
    let mut clauses: Vec<Clause> = Vec::new();
    for _ in 0..nclauses {
        let mut c: Clause = Vec::new();
        while c.len() < 3 {
            let v = next() % nvars;
            if c.iter().any(|l: &Lit| l.var == v) {
                continue;
            }
            c.push(if next() % 2 == 0 {
                Lit::pos(v)
            } else {
                Lit::neg(v)
            });
        }
        clauses.push(c);
    }
    Cnf::new(nvars, clauses)
}

#[test]
fn dpll_agrees_with_exhaustive_enumeration() {
    let nvars = 8;
    let mut sat = 0;
    let mut unsat = 0;
    for seed in 0..200u64 {
        // Sweep the clause density across the satisfiability threshold
        // so the batch contains both verdicts.
        let nclauses = 8 + (seed as usize % 30);
        let f = random_3cnf(seed * 7919 + 1, nvars, nclauses);
        let expected = f.brute_force();
        match (solve(&f), expected) {
            (SatOutcome::Sat(m), Some(_)) => {
                assert!(f.satisfied_by(&m), "seed {seed}: model does not check");
                sat += 1;
            }
            (SatOutcome::Unsat, None) => unsat += 1,
            (got, exp) => panic!(
                "seed {seed}: solver said {got:?}, enumeration said {}",
                if exp.is_some() { "SAT" } else { "UNSAT" }
            ),
        }
    }
    // The batch must exercise both verdicts, or the agreement is empty.
    assert!(
        sat > 0 && unsat > 0,
        "batch was one-sided: {sat} SAT, {unsat} UNSAT"
    );
}

// --- structural checks -----------------------------------------------

#[test]
fn every_satisfiable_answer_carries_a_checkable_total_model() {
    for seed in 0..50u64 {
        let f = random_3cnf(seed * 104_729 + 3, 6, 10 + (seed as usize % 10));
        if let SatOutcome::Sat(m) = solve(&f) {
            assert_eq!(m.len(), f.nvars, "model is not total");
            assert!(f.satisfied_by(&m));
        }
    }
}

#[test]
fn adding_a_clause_never_turns_unsat_into_sat() {
    // Monotonicity of refutation: a superset of an unsatisfiable clause
    // set is unsatisfiable. A cheap invariant the solver must respect.
    let base = pigeonhole(4, 3);
    let mut extended = base.clone();
    extended.clauses.push(vec![Lit::pos(0), Lit::pos(1)]);
    assert_eq!(solve(&base), SatOutcome::Unsat);
    assert_eq!(solve(&extended), SatOutcome::Unsat);
}
