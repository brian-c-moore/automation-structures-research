//! Rewrite rules and normalization.
//!
//! A rule `l -> r` rewrites a term `t` at position `p` when `l` matches
//! `t|_p` under some substitution `s`; the result is `t[r.apply(s)]_p`.
//! `normalize` applies leftmost-outermost steps until no redex remains.
//! Every rule set produced by completion is oriented by a reduction
//! order, so normalization terminates.

use super::term::{Subst, Term};
use super::unify::match_pattern;
use std::fmt;

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Rule {
    pub lhs: Term,
    pub rhs: Term,
}

impl Rule {
    pub fn new(lhs: Term, rhs: Term) -> Rule {
        Rule { lhs, rhs }
    }

    /// Rename the rule's variables to `prefix0, prefix1, ...` in order of
    /// first appearance. A rule denotes the same rewrite relation under
    /// any injective renaming, so this is used both to make two rules
    /// variable-disjoint before overlapping them and to put a finished
    /// system into a comparable form.
    pub fn rename(&self, prefix: &str) -> Rule {
        let mut vars = Vec::new();
        self.lhs.vars_into(&mut vars);
        self.rhs.vars_into(&mut vars);
        let mut map = Subst::new();
        for (i, v) in vars.iter().enumerate() {
            map.insert(v.clone(), Term::Var(format!("{prefix}{i}")));
        }
        Rule {
            lhs: self.lhs.apply(&map),
            rhs: self.rhs.apply(&map),
        }
    }

    /// The rule with variables renamed to `x0, x1, ...`.
    pub fn canonical(&self) -> Rule {
        self.rename("x")
    }
}

impl fmt::Display for Rule {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} -> {}", self.lhs, self.rhs)
    }
}

/// One leftmost-outermost rewrite step, or `None` if `t` is in normal
/// form with respect to `rules`.
pub fn rewrite_step(rules: &[Rule], t: &Term) -> Option<Term> {
    for r in rules {
        if let Some(s) = match_pattern(&r.lhs, t) {
            return Some(r.rhs.apply(&s));
        }
    }
    if let Term::App(f, args) = t {
        for (i, a) in args.iter().enumerate() {
            if let Some(reduced) = rewrite_step(rules, a) {
                let mut args = args.clone();
                args[i] = reduced;
                return Some(Term::App(f.clone(), args));
            }
        }
    }
    None
}

/// The normal form of `t` under `rules`.
pub fn normalize(rules: &[Rule], t: &Term) -> Term {
    let mut current = t.clone();
    while let Some(next) = rewrite_step(rules, &current) {
        current = next;
    }
    current
}

pub fn is_normal(rules: &[Rule], t: &Term) -> bool {
    rewrite_step(rules, t).is_none()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn normalizes_under_a_terminating_system() {
        // e*x -> x
        let r = Rule::new(
            Term::app("*", vec![Term::cst("e"), Term::var("x")]),
            Term::var("x"),
        );
        let t = Term::app(
            "*",
            vec![
                Term::cst("e"),
                Term::app("*", vec![Term::cst("e"), Term::cst("a")]),
            ],
        );
        assert_eq!(normalize(&[r], &t).to_string(), "a");
    }

    #[test]
    fn rewrites_inside_subterms() {
        let r = Rule::new(Term::cst("a"), Term::cst("b"));
        let t = Term::app("f", vec![Term::var("x"), Term::cst("a")]);
        assert_eq!(rewrite_step(&[r], &t).unwrap().to_string(), "f(x,b)");
    }

    #[test]
    fn canonical_renaming_is_stable() {
        let r = Rule::new(
            Term::app("*", vec![Term::var("u"), Term::var("w")]),
            Term::app("*", vec![Term::var("w"), Term::var("u")]),
        );
        assert_eq!(r.canonical().to_string(), "*(x0,x1) -> *(x1,x0)");
    }
}
