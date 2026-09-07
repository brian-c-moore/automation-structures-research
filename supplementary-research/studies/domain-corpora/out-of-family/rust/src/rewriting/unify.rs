//! Syntactic unification and one-way matching.
//!
//! `unify` is Robinson unification with the occurs check: it returns a
//! most general unifier, or `None` when the two terms have none.
//! `match_pattern` is the one-way variant used by rewriting: only the
//! pattern's variables may be bound.

use super::term::{Subst, Term};

/// Extend `subst` with `x := t`, propagating the new binding into the
/// bindings already recorded.
fn bind(subst: &mut Subst, x: String, t: Term) {
    let mut single = Subst::new();
    single.insert(x.clone(), t.clone());
    for v in subst.values_mut() {
        *v = v.apply(&single);
    }
    subst.insert(x, t);
}

/// A most general unifier of `s` and `t`, or `None`.
pub fn unify(s: &Term, t: &Term) -> Option<Subst> {
    let mut subst = Subst::new();
    let mut pending = vec![(s.clone(), t.clone())];
    while let Some((a, b)) = pending.pop() {
        let a = a.apply(&subst);
        let b = b.apply(&subst);
        if a == b {
            continue;
        }
        match (a, b) {
            (Term::Var(x), other) => {
                if other.has_var(&x) {
                    return None; // occurs check
                }
                bind(&mut subst, x, other);
            }
            (other, Term::Var(y)) => {
                if other.has_var(&y) {
                    return None; // occurs check
                }
                bind(&mut subst, y, other);
            }
            (Term::App(f, fargs), Term::App(g, gargs)) => {
                if f != g || fargs.len() != gargs.len() {
                    return None;
                }
                for pair in fargs.into_iter().zip(gargs) {
                    pending.push(pair);
                }
            }
        }
    }
    Some(subst)
}

/// A substitution `s` with `pattern.apply(s) == term`, or `None`. Only
/// the pattern's variables are bound; `term` is treated as ground data.
pub fn match_pattern(pattern: &Term, term: &Term) -> Option<Subst> {
    let mut subst = Subst::new();
    let mut pending = vec![(pattern.clone(), term.clone())];
    while let Some((p, u)) = pending.pop() {
        match p {
            Term::Var(x) => match subst.get(&x) {
                Some(bound) => {
                    if *bound != u {
                        return None;
                    }
                }
                None => {
                    subst.insert(x, u);
                }
            },
            Term::App(f, pargs) => match u {
                Term::App(g, uargs) if f == g && pargs.len() == uargs.len() => {
                    for pair in pargs.into_iter().zip(uargs) {
                        pending.push(pair);
                    }
                }
                _ => return None,
            },
        }
    }
    Some(subst)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unifies_and_applies() {
        // f(x, b) vs f(a, y)
        let s = Term::app("f", vec![Term::var("x"), Term::cst("b")]);
        let t = Term::app("f", vec![Term::cst("a"), Term::var("y")]);
        let mgu = unify(&s, &t).expect("unifiable");
        assert_eq!(s.apply(&mgu), t.apply(&mgu));
        assert_eq!(s.apply(&mgu).to_string(), "f(a,b)");
    }

    #[test]
    fn occurs_check_blocks_cyclic_binding() {
        // x vs f(x)
        let s = Term::var("x");
        let t = Term::app("f", vec![Term::var("x")]);
        assert!(unify(&s, &t).is_none());
    }

    #[test]
    fn clashing_symbols_do_not_unify() {
        assert!(unify(&Term::cst("a"), &Term::cst("b")).is_none());
    }

    #[test]
    fn matching_is_one_way() {
        let pat = Term::app("f", vec![Term::var("x"), Term::var("x")]);
        let ok = Term::app("f", vec![Term::cst("a"), Term::cst("a")]);
        let bad = Term::app("f", vec![Term::cst("a"), Term::cst("b")]);
        assert!(match_pattern(&pat, &ok).is_some());
        assert!(match_pattern(&pat, &bad).is_none());
        // A variable in the subject is not bindable.
        assert!(match_pattern(&Term::cst("a"), &Term::var("x")).is_none());
    }
}
