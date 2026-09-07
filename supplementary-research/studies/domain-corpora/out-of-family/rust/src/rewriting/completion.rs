//! **Knuth-Bendix completion** (Knuth & Bendix 1970; the
//! interreducing formulation of Huet 1981).
//!
//! Input: a set of equations and a reduction order. Output, when the
//! procedure succeeds: a terminating, confluent rewrite system that
//! decides the equational theory of the input — every equation's two
//! sides share a normal form, and no others do.
//!
//! The procedure maintains a set `E` of equations still to be processed
//! and a set `R` of oriented rules. Each round:
//!
//! 1. take the smallest equation out of `E` and normalize both sides
//!    under `R`; drop it if the sides became identical;
//! 2. orient it with the reduction order — fail if neither direction is
//!    ordered (the published failure mode, e.g. commutativity);
//! 3. interreduce `R` against the new rule: rules whose left-hand side
//!    the new rule reduces are *collapsed* back into `E`; the remaining
//!    rules' right-hand sides are *composed* (reduced) by it;
//! 4. add every critical pair between the new rule and `R` (including
//!    the new rule with itself) to `E`.
//!
//! `E` empty means every critical pair of `R` is joinable, so `R` is
//! locally confluent; `R` is terminating because the reduction order
//! oriented it; by Newman's lemma `R` is confluent. Interreduction makes
//! the output the *reduced* canonical system, which for a given
//! reduction order is unique up to variable renaming — that uniqueness
//! is what makes a published completion a usable reference anchor.

use super::critical_pairs::critical_pairs;
use super::order::{lpo_gt, Precedence};
use super::rewrite::{is_normal, normalize, Rule};
use super::term::Term;

/// What a completion run produced.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum CompletionOutcome {
    /// A terminating, confluent, reduced rewrite system.
    Complete(Vec<Rule>),
    /// An equation neither direction of which the reduction order
    /// orients. Completion fails; this is a property of the equation and
    /// the order, not a defect of the procedure.
    Unorientable { left: Term, right: Term },
    /// The round limit was reached with equations still pending.
    /// Completion is a semi-decision procedure: it may run forever.
    LimitReached { rules: Vec<Rule>, pending: usize },
}

/// Run completion over `axioms` with the LPO induced by `prec`, for at
/// most `max_rounds` rounds.
pub fn complete(
    axioms: &[(Term, Term)],
    prec: &Precedence,
    max_rounds: usize,
) -> CompletionOutcome {
    let mut equations: Vec<(Term, Term)> = axioms.to_vec();
    let mut rules: Vec<Rule> = Vec::new();

    for _ in 0..max_rounds {
        if equations.is_empty() {
            return CompletionOutcome::Complete(rules.iter().map(Rule::canonical).collect());
        }

        // 1. Smallest equation first — the standard fairness heuristic:
        //    every equation is eventually selected because processing
        //    only ever adds larger ones.
        let pick = smallest(&equations);
        let (s, t) = equations.remove(pick);
        let s = normalize(&rules, &s);
        let t = normalize(&rules, &t);
        if s == t {
            continue;
        }

        // 2. Orient.
        let new_rule = if lpo_gt(prec, &s, &t) {
            Rule::new(s, t)
        } else if lpo_gt(prec, &t, &s) {
            Rule::new(t, s)
        } else {
            return CompletionOutcome::Unorientable { left: s, right: t };
        };

        // 3. Interreduce: collapse, then compose.
        let only_new = [new_rule.clone()];
        let mut kept: Vec<Rule> = Vec::new();
        for r in rules.drain(..) {
            if !is_normal(&only_new, &r.lhs) {
                equations.push((r.lhs, r.rhs)); // collapse
            } else {
                let rhs = normalize(&only_new, &r.rhs); // compose
                kept.push(Rule::new(r.lhs, rhs));
            }
        }
        rules = kept;

        // 4. Critical pairs with the surviving rules and with itself.
        let mut fresh: Vec<(Term, Term)> = Vec::new();
        for r in &rules {
            fresh.extend(critical_pairs(r, &new_rule));
            fresh.extend(critical_pairs(&new_rule, r));
        }
        fresh.extend(critical_pairs(&new_rule, &new_rule));

        rules.push(new_rule);

        for (a, b) in fresh {
            let a = normalize(&rules, &a);
            let b = normalize(&rules, &b);
            if a != b {
                equations.push((a, b));
            }
        }
    }

    CompletionOutcome::LimitReached {
        rules: rules.iter().map(Rule::canonical).collect(),
        pending: equations.len(),
    }
}

fn smallest(equations: &[(Term, Term)]) -> usize {
    let mut best = 0;
    let mut best_size = usize::MAX;
    for (i, (s, t)) in equations.iter().enumerate() {
        let size = s.size() + t.size();
        if size < best_size {
            best_size = size;
            best = i;
        }
    }
    best
}

// ---------------------------------------------------------------------
// Independent checks on a finished system.
//
// These do not trust the procedure: they re-derive the properties a
// completion is supposed to have, from the rule set alone.
// ---------------------------------------------------------------------

/// Every critical pair of `rules` has a common normal form. With
/// termination (guaranteed by the reduction order that oriented the
/// rules) this is confluence, by the Critical Pair Lemma plus Newman's
/// lemma.
pub fn locally_confluent(rules: &[Rule]) -> bool {
    unjoinable_critical_pairs(rules).is_empty()
}

/// The critical pairs that fail to join, for reporting.
pub fn unjoinable_critical_pairs(rules: &[Rule]) -> Vec<(Term, Term)> {
    let mut bad = Vec::new();
    for a in rules {
        for b in rules {
            for (l, r) in critical_pairs(a, b) {
                if normalize(rules, &l) != normalize(rules, &r) {
                    bad.push((l, r));
                }
            }
        }
    }
    bad
}

/// No rule's left-hand side is reducible by the other rules, and every
/// right-hand side is in normal form. This is what interreduction buys,
/// and it is the condition under which the canonical system is unique
/// for a given reduction order.
pub fn is_reduced(rules: &[Rule]) -> bool {
    for (i, r) in rules.iter().enumerate() {
        let others: Vec<Rule> = rules
            .iter()
            .enumerate()
            .filter(|(j, _)| *j != i)
            .map(|(_, x)| x.clone())
            .collect();
        if !is_normal(&others, &r.lhs) {
            return false;
        }
        if !is_normal(rules, &r.rhs) {
            return false;
        }
    }
    true
}

/// Every rule is oriented by the given order — the termination witness.
pub fn all_oriented(prec: &Precedence, rules: &[Rule]) -> bool {
    rules.iter().all(|r| lpo_gt(prec, &r.lhs, &r.rhs))
}

/// Every input equation is decided by `rules`: both sides reach the same
/// normal form. Soundness of the completion with respect to its input.
pub fn decides(rules: &[Rule], axioms: &[(Term, Term)]) -> bool {
    axioms
        .iter()
        .all(|(s, t)| normalize(rules, s) == normalize(rules, t))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn an_already_canonical_system_is_returned_unchanged() {
        // Peano addition: no overlaps, nothing to add.
        let axioms = vec![
            (
                Term::app("plus", vec![Term::cst("0"), Term::var("y")]),
                Term::var("y"),
            ),
            (
                Term::app(
                    "plus",
                    vec![Term::app("s", vec![Term::var("x")]), Term::var("y")],
                ),
                Term::app(
                    "s",
                    vec![Term::app("plus", vec![Term::var("x"), Term::var("y")])],
                ),
            ),
        ];
        let prec = Precedence::ascending(&["0", "s", "plus"]);
        match complete(&axioms, &prec, 100) {
            CompletionOutcome::Complete(rules) => {
                assert_eq!(rules.len(), 2);
                assert!(locally_confluent(&rules));
                assert!(decides(&rules, &axioms));
            }
            other => panic!("expected Complete, got {other:?}"),
        }
    }

    #[test]
    fn an_involution_completes_to_one_rule() {
        // f(f(x)) = x
        let axioms = vec![(
            Term::app("f", vec![Term::app("f", vec![Term::var("x")])]),
            Term::var("x"),
        )];
        let prec = Precedence::ascending(&["f"]);
        match complete(&axioms, &prec, 100) {
            CompletionOutcome::Complete(rules) => {
                assert_eq!(rules.len(), 1);
                assert_eq!(rules[0].to_string(), "f(f(x0)) -> x0");
            }
            other => panic!("expected Complete, got {other:?}"),
        }
    }
}
