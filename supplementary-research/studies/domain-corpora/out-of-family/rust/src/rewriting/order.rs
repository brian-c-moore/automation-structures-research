//! The lexicographic path order (LPO), the reduction order Knuth-Bendix
//! completion uses to orient equations.
//!
//! Given a strict precedence `>` on function symbols, `s >_lpo t` holds
//! when `s = f(s_1..s_m)` and one of:
//!
//! 1. `t` is a variable occurring properly in `s`;
//! 2. some `s_i >=_lpo t`;
//! 3. `t = g(t_1..t_n)`, `f > g`, and `s >_lpo t_j` for every `j`;
//! 4. `t = g(t_1..t_n)`, `f = g`, `(s_1..s_m) >_lex (t_1..t_n)`, and
//!    `s >_lpo t_j` for every `j`.
//!
//! LPO is a simplification order, hence well-founded on terms over a
//! finite signature: an oriented rule set is terminating by construction.

use super::term::Term;
use std::collections::BTreeMap;

/// A strict precedence on function symbols. Symbols listed later are
/// greater; symbols absent from the list are least.
#[derive(Clone, Debug, Default)]
pub struct Precedence {
    ranks: BTreeMap<String, usize>,
}

impl Precedence {
    /// Build a precedence from symbols in ascending order (least first).
    pub fn ascending(symbols: &[&str]) -> Precedence {
        let mut ranks = BTreeMap::new();
        for (i, s) in symbols.iter().enumerate() {
            ranks.insert((*s).to_string(), i + 1);
        }
        Precedence { ranks }
    }

    fn rank(&self, f: &str) -> usize {
        *self.ranks.get(f).unwrap_or(&0)
    }

    pub fn gt(&self, f: &str, g: &str) -> bool {
        self.rank(f) > self.rank(g)
    }
}

/// `s >_lpo t`.
pub fn lpo_gt(prec: &Precedence, s: &Term, t: &Term) -> bool {
    if s == t {
        return false;
    }
    let (f, sargs) = match s {
        Term::Var(_) => return false, // a variable is greater than nothing
        Term::App(f, args) => (f, args),
    };
    // Case 2 applies whatever t is.
    if sargs.iter().any(|si| si == t || lpo_gt(prec, si, t)) {
        return true;
    }
    match t {
        // Case 1.
        Term::Var(x) => s.has_var(x),
        Term::App(g, targs) => {
            let dominates_args = || targs.iter().all(|tj| lpo_gt(prec, s, tj));
            // Case 3.
            if prec.gt(f, g) && dominates_args() {
                return true;
            }
            // Case 4.
            if f == g && sargs.len() == targs.len() && lex_gt(prec, sargs, targs) {
                return dominates_args();
            }
            false
        }
    }
}

fn lex_gt(prec: &Precedence, ss: &[Term], ts: &[Term]) -> bool {
    for (a, b) in ss.iter().zip(ts) {
        if a == b {
            continue;
        }
        return lpo_gt(prec, a, b);
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;

    fn group_prec() -> Precedence {
        // e < * < i
        Precedence::ascending(&["e", "*", "i"])
    }

    fn m(a: Term, b: Term) -> Term {
        Term::app("*", vec![a, b])
    }
    fn inv(a: Term) -> Term {
        Term::app("i", vec![a])
    }
    fn x() -> Term {
        Term::var("x")
    }
    fn y() -> Term {
        Term::var("y")
    }
    fn z() -> Term {
        Term::var("z")
    }

    #[test]
    fn proper_subterms_are_smaller() {
        let p = group_prec();
        assert!(lpo_gt(&p, &m(x(), y()), &x()));
        assert!(!lpo_gt(&p, &x(), &m(x(), y())));
    }

    #[test]
    fn associativity_orients_left_to_right() {
        let p = group_prec();
        let lhs = m(m(x(), y()), z());
        let rhs = m(x(), m(y(), z()));
        assert!(lpo_gt(&p, &lhs, &rhs));
        assert!(!lpo_gt(&p, &rhs, &lhs));
    }

    #[test]
    fn inverse_distributes_by_precedence() {
        let p = group_prec();
        let lhs = inv(m(x(), y()));
        let rhs = m(inv(y()), inv(x()));
        assert!(lpo_gt(&p, &lhs, &rhs));
    }

    #[test]
    fn commutativity_is_unorientable() {
        let p = group_prec();
        let lhs = m(x(), y());
        let rhs = m(y(), x());
        assert!(!lpo_gt(&p, &lhs, &rhs));
        assert!(!lpo_gt(&p, &rhs, &lhs));
    }

    #[test]
    fn irreflexive() {
        let p = group_prec();
        assert!(!lpo_gt(&p, &m(x(), y()), &m(x(), y())));
    }
}
