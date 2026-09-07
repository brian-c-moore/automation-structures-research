//! Reference validation for **Knuth-Bendix completion**.
//!
//! Two independent kinds of check, both external to the implementation:
//!
//! * **Literature anchor.** Completing the group axioms under the LPO
//!   with precedence `i > * > e` is the published example of the method
//!   (Knuth & Bendix 1970; reproduced in Baader & Nipkow, *Term Rewriting
//!   and All That*): the canonical ten-rule system. Because a reduced
//!   canonical system is unique up to variable renaming for a fixed
//!   reduction order, this is a rule-for-rule reference output, not a
//!   sample of one possible answer.
//! * **Structural re-derivation.** The finished system is checked against
//!   the properties a completion is supposed to have, computed from the
//!   rule set alone: every rule oriented by the order (termination),
//!   every critical pair joinable (local confluence, hence confluence),
//!   reducedness, and soundness against the input axioms. A negative
//!   control confirms the system is not deciding everything.

use dac_out_of_family::rewriting::completion::{
    all_oriented, decides, is_reduced, locally_confluent, unjoinable_critical_pairs,
};
use dac_out_of_family::rewriting::rewrite::normalize;
use dac_out_of_family::{complete, CompletionOutcome, Precedence, Rule, Term};

// --- signature helpers ------------------------------------------------

fn mul(a: Term, b: Term) -> Term {
    Term::app("*", vec![a, b])
}
fn inv(a: Term) -> Term {
    Term::app("i", vec![a])
}
fn e() -> Term {
    Term::cst("e")
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

/// e*x = x, i(x)*x = e, (x*y)*z = x*(y*z)
fn group_axioms() -> Vec<(Term, Term)> {
    vec![
        (mul(e(), x()), x()),
        (mul(inv(x()), x()), e()),
        (mul(mul(x(), y()), z()), mul(x(), mul(y(), z()))),
    ]
}

fn group_precedence() -> Precedence {
    Precedence::ascending(&["e", "*", "i"])
}

fn shown(rules: &[Rule]) -> Vec<String> {
    let mut v: Vec<String> = rules.iter().map(|r| r.to_string()).collect();
    v.sort();
    v
}

fn completed_group() -> Vec<Rule> {
    match complete(&group_axioms(), &group_precedence(), 1000) {
        CompletionOutcome::Complete(rules) => rules,
        other => panic!("group completion did not succeed: {other:?}"),
    }
}

// --- the literature anchor -------------------------------------------

#[test]
fn group_completion_reproduces_the_published_canonical_system() {
    let rules = completed_group();
    let mut expected: Vec<String> = vec![
        "*(e,x0) -> x0",
        "*(i(x0),x0) -> e",
        "*(*(x0,x1),x2) -> *(x0,*(x1,x2))",
        "*(i(x0),*(x0,x1)) -> x1",
        "*(x0,e) -> x0",
        "i(e) -> e",
        "i(i(x0)) -> x0",
        "*(x0,i(x0)) -> e",
        "*(x0,*(i(x0),x1)) -> x1",
        "i(*(x0,x1)) -> *(i(x1),i(x0))",
    ]
    .into_iter()
    .map(str::to_string)
    .collect();
    expected.sort();
    assert_eq!(shown(&rules), expected);
}

// --- structural re-derivation ----------------------------------------

#[test]
fn group_completion_is_terminating_confluent_and_reduced() {
    let rules = completed_group();
    let prec = group_precedence();
    assert!(
        all_oriented(&prec, &rules),
        "a rule is not oriented by the reduction order"
    );
    let bad = unjoinable_critical_pairs(&rules);
    assert!(bad.is_empty(), "unjoinable critical pairs: {bad:?}");
    assert!(locally_confluent(&rules));
    assert!(is_reduced(&rules), "the system is not interreduced");
    assert!(
        decides(&rules, &group_axioms()),
        "the system does not decide its own axioms"
    );
}

#[test]
fn group_completion_decides_known_consequences() {
    let rules = completed_group();
    // Theorems of group theory, each an equation the canonical system
    // must join, and none of them an input axiom.
    let consequences = vec![
        (inv(inv(x())), x()),
        (mul(x(), inv(x())), e()),
        (inv(mul(x(), y())), mul(inv(y()), inv(x()))),
        (inv(e()), e()),
        (mul(x(), e()), x()),
        (mul(inv(x()), mul(x(), y())), y()),
    ];
    for (l, r) in consequences {
        assert_eq!(
            normalize(&rules, &l),
            normalize(&rules, &r),
            "not decided: {l} = {r}"
        );
    }
}

#[test]
fn group_completion_does_not_decide_a_non_consequence() {
    // Negative control: commutativity is not a theorem of group theory,
    // so the canonical system must keep the two sides apart. Without
    // this the "decides" checks above would pass for a system that
    // collapses everything.
    let rules = completed_group();
    let l = mul(x(), y());
    let r = mul(y(), x());
    assert_ne!(normalize(&rules, &l), normalize(&rules, &r));
}

// --- further anchors --------------------------------------------------

#[test]
fn monoid_axioms_are_already_canonical() {
    // e*x = x, x*e = x, (x*y)*z = x*(y*z): every critical pair joins, so
    // completion adds nothing.
    let axioms = vec![
        (mul(e(), x()), x()),
        (mul(x(), e()), x()),
        (mul(mul(x(), y()), z()), mul(x(), mul(y(), z()))),
    ];
    let prec = Precedence::ascending(&["e", "*"]);
    match complete(&axioms, &prec, 1000) {
        CompletionOutcome::Complete(rules) => {
            assert_eq!(
                shown(&rules),
                vec![
                    "*(*(x0,x1),x2) -> *(x0,*(x1,x2))".to_string(),
                    "*(e,x0) -> x0".to_string(),
                    "*(x0,e) -> x0".to_string(),
                ]
            );
            assert!(locally_confluent(&rules));
            assert!(is_reduced(&rules));
        }
        other => panic!("expected Complete, got {other:?}"),
    }
}

#[test]
fn commutativity_is_the_published_failure_case() {
    // No reduction order orients x*y = y*x: the two sides are renamings
    // of each other. Completion reports the failure rather than looping.
    let axioms = vec![(mul(x(), y()), mul(y(), x()))];
    let prec = Precedence::ascending(&["*"]);
    match complete(&axioms, &prec, 1000) {
        CompletionOutcome::Unorientable { left, right } => {
            assert_eq!(left.to_string(), "*(x,y)");
            assert_eq!(right.to_string(), "*(y,x)");
        }
        other => panic!("expected Unorientable, got {other:?}"),
    }
}
