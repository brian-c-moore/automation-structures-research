//! Propositional formulas in conjunctive normal form, and the two
//! things one can independently do with a model: check it, and find one
//! by exhaustion.

use std::collections::BTreeMap;

pub type Var = usize;

/// A literal: a variable, positive or negated.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Lit {
    pub var: Var,
    pub sign: bool,
}

impl Lit {
    pub fn pos(var: Var) -> Lit {
        Lit { var, sign: true }
    }
    pub fn neg(var: Var) -> Lit {
        Lit { var, sign: false }
    }
    pub fn negate(self) -> Lit {
        Lit {
            var: self.var,
            sign: !self.sign,
        }
    }
    pub fn holds(self, model: &Model) -> Option<bool> {
        model.get(&self.var).map(|v| *v == self.sign)
    }
}

/// A disjunction of literals.
pub type Clause = Vec<Lit>;

/// A total assignment of truth values to variables.
pub type Model = BTreeMap<Var, bool>;

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Cnf {
    pub nvars: usize,
    pub clauses: Vec<Clause>,
}

impl Cnf {
    pub fn new(nvars: usize, clauses: Vec<Clause>) -> Cnf {
        Cnf { nvars, clauses }
    }

    /// Does `model` satisfy every clause? The independent check applied
    /// to whatever the solver returns.
    pub fn satisfied_by(&self, model: &Model) -> bool {
        self.clauses
            .iter()
            .all(|c| c.iter().any(|l| l.holds(model) == Some(true)))
    }

    /// A satisfying model found by enumerating all `2^nvars`
    /// assignments — a second oracle by a different method, for
    /// cross-checking the solver on small instances.
    pub fn brute_force(&self) -> Option<Model> {
        assert!(self.nvars <= 20, "exhaustive search is for small instances");
        for bits in 0u32..(1u32 << self.nvars) {
            let model: Model = (0..self.nvars).map(|v| (v, bits >> v & 1 == 1)).collect();
            if self.satisfied_by(&model) {
                return Some(model);
            }
        }
        None
    }
}

/// The pigeonhole formula: `pigeons` pigeons into `holes` holes, each
/// pigeon somewhere, no two pigeons sharing a hole. Unsatisfiable
/// exactly when `pigeons > holes` — the standard hard UNSAT family.
pub fn pigeonhole(pigeons: usize, holes: usize) -> Cnf {
    let var = |p: usize, h: usize| p * holes + h;
    let mut clauses = Vec::new();
    for p in 0..pigeons {
        clauses.push((0..holes).map(|h| Lit::pos(var(p, h))).collect());
    }
    for h in 0..holes {
        for q in 0..pigeons {
            for p in 0..q {
                clauses.push(vec![Lit::neg(var(p, h)), Lit::neg(var(q, h))]);
            }
        }
    }
    Cnf::new(pigeons * holes, clauses)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn model_checking_agrees_with_the_definition() {
        // (x0 or x1) and (not x0)
        let f = Cnf::new(2, vec![vec![Lit::pos(0), Lit::pos(1)], vec![Lit::neg(0)]]);
        let good: Model = [(0, false), (1, true)].into_iter().collect();
        let bad: Model = [(0, false), (1, false)].into_iter().collect();
        assert!(f.satisfied_by(&good));
        assert!(!f.satisfied_by(&bad));
    }

    #[test]
    fn brute_force_matches_the_pigeonhole_principle() {
        assert!(pigeonhole(2, 2).brute_force().is_some());
        assert!(pigeonhole(3, 2).brute_force().is_none());
    }

    #[test]
    fn the_empty_clause_is_unsatisfiable_and_the_empty_formula_is_not() {
        assert!(Cnf::new(1, vec![]).brute_force().is_some());
        assert!(Cnf::new(1, vec![vec![]]).brute_force().is_none());
    }
}
