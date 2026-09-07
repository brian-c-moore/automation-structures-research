//! Critical pairs.
//!
//! Two rules overlap when the left-hand side of one unifies with a
//! non-variable subterm of the other. Overlapping `l2 -> r2` into
//! `l1 -> r1` at a non-variable position `p` of `l1` with most general
//! unifier `s` yields the critical pair
//!
//! ```text
//! ( (l1[r2]_p).apply(s) , r1.apply(s) )
//! ```
//!
//! the two results of reducing the overlapped term `l1.apply(s)` in the
//! two possible ways. By the Critical Pair Lemma a terminating system is
//! confluent exactly when every critical pair is joinable, which is why
//! completion's job is to make them so.

use super::rewrite::Rule;
use super::term::Term;
use super::unify::unify;

/// Critical pairs obtained by overlapping `inner` into `outer`. The root
/// overlap of a rule with itself is excluded: it is trivial.
pub fn critical_pairs(outer: &Rule, inner: &Rule) -> Vec<(Term, Term)> {
    let same_rule = outer.canonical() == inner.canonical();
    // Rename apart: overlapping requires the two rules to share no
    // variables.
    let o = outer.rename("u");
    let i = inner.rename("v");

    let mut pairs = Vec::new();
    for p in o.lhs.nonvar_positions() {
        if same_rule && p.is_empty() {
            continue;
        }
        let sub = match o.lhs.at(&p) {
            Some(t) => t,
            None => continue,
        };
        if let Some(s) = unify(sub, &i.lhs) {
            let left = o.lhs.replace_at(&p, &i.rhs).apply(&s);
            let right = o.rhs.apply(&s);
            if left != right {
                pairs.push((left, right));
            }
        }
    }
    pairs
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn textbook_overlap_of_associativity_and_left_inverse() {
        // The first critical pair of the group completion: reducing
        // (i(x)*x)*z by associativity gives i(x)*(x*z), by the inverse
        // rule gives e*z.
        let assoc = Rule::new(
            Term::app(
                "*",
                vec![
                    Term::app("*", vec![Term::var("x"), Term::var("y")]),
                    Term::var("z"),
                ],
            ),
            Term::app(
                "*",
                vec![
                    Term::var("x"),
                    Term::app("*", vec![Term::var("y"), Term::var("z")]),
                ],
            ),
        );
        let left_inv = Rule::new(
            Term::app(
                "*",
                vec![Term::app("i", vec![Term::var("x")]), Term::var("x")],
            ),
            Term::cst("e"),
        );
        let cps = critical_pairs(&assoc, &left_inv);
        assert_eq!(cps.len(), 1, "got {cps:?}");
        let (a, b) = &cps[0];
        assert_eq!(a.to_string(), "*(e,u2)");
        assert_eq!(b.to_string(), "*(i(v0),*(v0,u2))");
        // The reverse direction has no overlap.
        assert!(critical_pairs(&left_inv, &assoc).is_empty());
    }

    #[test]
    fn a_rule_has_no_trivial_self_overlap_at_the_root() {
        let r = Rule::new(
            Term::app("f", vec![Term::app("f", vec![Term::var("x")])]),
            Term::var("x"),
        );
        // The only overlap is f(f(f(x))): both reducts are f(x), so the
        // pair is dropped as trivially joinable at construction.
        let cps = critical_pairs(&r, &r);
        assert!(cps.is_empty(), "unexpected critical pairs: {cps:?}");
    }

    #[test]
    fn non_overlapping_rules_produce_nothing() {
        let a = Rule::new(Term::app("f", vec![Term::var("x")]), Term::var("x"));
        let b = Rule::new(Term::app("g", vec![Term::var("x")]), Term::var("x"));
        assert!(critical_pairs(&a, &b).is_empty());
        assert!(critical_pairs(&b, &a).is_empty());
    }
}
