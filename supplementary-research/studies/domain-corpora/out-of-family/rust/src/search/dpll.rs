//! **The DPLL procedure** (Davis, Logemann & Loveland 1962).
//!
//! The published formulation, which searches by *simplifying the
//! formula*: `F|l` drops every clause containing `l` and deletes `~l`
//! from the rest. Each call
//!
//! 1. runs unit propagation to a fixed point — a one-literal clause
//!    forces its literal, which simplifies the formula and may expose
//!    further units;
//! 2. runs pure-literal elimination to a fixed point — a variable
//!    occurring at only one polarity can be set to satisfy every clause
//!    it appears in, which may make further literals pure;
//! 3. answers immediately if no clauses remain (satisfiable) or some
//!    clause is empty (this branch is refuted);
//! 4. otherwise picks a literal and tries both polarities in turn.
//!
//! This is the procedure as published: the state of a branch is the
//! simplified formula passed down, so nothing is mutated and nothing has
//! to be undone. A trail-based implementation — the form modern solvers
//! use, and the basis for conflict-driven learning — would instead mutate
//! one shared assignment and hold an explicit stack to unwind it.

use super::cnf::{Clause, Cnf, Lit, Model, Var};
use std::collections::BTreeSet;

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum SatOutcome {
    Sat(Model),
    Unsat,
    /// The node budget ran out. DPLL always terminates, so this only
    /// fires when the caller sets a budget below the search's size.
    LimitReached,
}

/// Solve `cnf`, exploring at most `max_nodes` search nodes.
pub fn solve(cnf: &Cnf, max_nodes: usize) -> SatOutcome {
    let mut budget = max_nodes;
    match dpll(cnf.clauses.clone(), Model::new(), &mut budget) {
        Branch::Sat(partial) => SatOutcome::Sat(total(cnf.nvars, partial)),
        Branch::Unsat => SatOutcome::Unsat,
        Branch::Exhausted => SatOutcome::LimitReached,
    }
}

enum Branch {
    Sat(Model),
    Unsat,
    Exhausted,
}

fn dpll(mut clauses: Vec<Clause>, mut assign: Model, budget: &mut usize) -> Branch {
    if *budget == 0 {
        return Branch::Exhausted;
    }
    *budget -= 1;

    // 1. Unit propagation.
    loop {
        if clauses.iter().any(|c| c.is_empty()) {
            return Branch::Unsat;
        }
        match clauses.iter().find(|c| c.len() == 1).map(|c| c[0]) {
            None => break,
            Some(l) => {
                assign.insert(l.var, l.sign);
                clauses = simplify(&clauses, l);
            }
        }
    }

    // 2. Pure-literal elimination.
    while let Some(l) = pure_literal(&clauses) {
        assign.insert(l.var, l.sign);
        clauses = simplify(&clauses, l);
    }

    // 3. Answer if this branch is settled.
    if clauses.iter().any(|c| c.is_empty()) {
        return Branch::Unsat;
    }
    if clauses.is_empty() {
        return Branch::Sat(assign);
    }

    // 4. Split on a literal, trying both polarities.
    let l = clauses[0][0];
    let mut left = assign.clone();
    left.insert(l.var, l.sign);
    match dpll(simplify(&clauses, l), left, budget) {
        Branch::Sat(m) => return Branch::Sat(m),
        Branch::Exhausted => return Branch::Exhausted,
        Branch::Unsat => {}
    }
    let n = l.negate();
    let mut right = assign;
    right.insert(n.var, n.sign);
    dpll(simplify(&clauses, n), right, budget)
}

/// `F|l`: drop the clauses `l` satisfies, delete `~l` from the rest.
fn simplify(clauses: &[Clause], l: Lit) -> Vec<Clause> {
    let n = l.negate();
    clauses
        .iter()
        .filter(|c| !c.contains(&l))
        .map(|c| c.iter().copied().filter(|x| *x != n).collect())
        .collect()
}

/// A literal whose complement occurs nowhere in the formula.
fn pure_literal(clauses: &[Clause]) -> Option<Lit> {
    let mut occurring: BTreeSet<Lit> = BTreeSet::new();
    for c in clauses {
        for l in c {
            occurring.insert(*l);
        }
    }
    occurring
        .iter()
        .copied()
        .find(|l| !occurring.contains(&l.negate()))
}

/// Extend a partial model to every variable. Variables the search never
/// assigned occur in no surviving clause, so any value will do.
fn total(nvars: usize, partial: Model) -> Model {
    (0..nvars as Var)
        .map(|v| (v, partial.get(&v).copied().unwrap_or(true)))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::super::cnf::pigeonhole;
    use super::*;

    const BUDGET: usize = 1_000_000;

    #[test]
    fn trivial_formulas() {
        // No clauses: satisfied vacuously.
        assert!(matches!(
            solve(&Cnf::new(1, vec![]), BUDGET),
            SatOutcome::Sat(_)
        ));
        // The empty clause: refuted immediately.
        assert_eq!(solve(&Cnf::new(1, vec![vec![]]), BUDGET), SatOutcome::Unsat);
        // x and not x.
        let f = Cnf::new(1, vec![vec![Lit::pos(0)], vec![Lit::neg(0)]]);
        assert_eq!(solve(&f, BUDGET), SatOutcome::Unsat);
    }

    #[test]
    fn unit_propagation_settles_a_chain() {
        // x0, (~x0 or x1), (~x1 or x2)  forces all three true.
        let f = Cnf::new(
            3,
            vec![
                vec![Lit::pos(0)],
                vec![Lit::neg(0), Lit::pos(1)],
                vec![Lit::neg(1), Lit::pos(2)],
            ],
        );
        match solve(&f, BUDGET) {
            SatOutcome::Sat(m) => {
                assert_eq!(m[&0], true);
                assert_eq!(m[&1], true);
                assert_eq!(m[&2], true);
            }
            other => panic!("expected Sat, got {other:?}"),
        }
    }

    #[test]
    fn the_budget_is_honoured() {
        // One node is not enough to refute the pigeonhole formula.
        assert_eq!(solve(&pigeonhole(4, 3), 1), SatOutcome::LimitReached);
    }
}
