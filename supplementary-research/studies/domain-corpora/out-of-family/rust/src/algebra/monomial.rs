//! Monomials as exponent vectors, and the three standard monomial
//! orders.
//!
//! A monomial order is a total order on monomials that is compatible
//! with multiplication (`a > b` implies `a*c > b*c`) and is a well-order
//! (every non-empty set has a least element). The second property is
//! what makes the division algorithm terminate; like the reduction order
//! in completion, it is a contract on the order supplied, not something
//! any pass checks at run time.

use std::cmp::Ordering;
use std::fmt::Write as _;

/// Exponent vector over a fixed number of variables.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Monomial {
    pub exps: Vec<u32>,
}

impl Monomial {
    pub fn new(exps: Vec<u32>) -> Monomial {
        Monomial { exps }
    }

    pub fn one(nvars: usize) -> Monomial {
        Monomial {
            exps: vec![0; nvars],
        }
    }

    pub fn nvars(&self) -> usize {
        self.exps.len()
    }

    pub fn total_degree(&self) -> u32 {
        self.exps.iter().sum()
    }

    pub fn is_one(&self) -> bool {
        self.exps.iter().all(|e| *e == 0)
    }

    pub fn mul(&self, other: &Monomial) -> Monomial {
        Monomial {
            exps: self
                .exps
                .iter()
                .zip(&other.exps)
                .map(|(a, b)| a + b)
                .collect(),
        }
    }

    /// Does `self` divide `other`?
    pub fn divides(&self, other: &Monomial) -> bool {
        self.exps.iter().zip(&other.exps).all(|(a, b)| a <= b)
    }

    /// `self / other`, when `other` divides `self`.
    pub fn div(&self, other: &Monomial) -> Option<Monomial> {
        if !other.divides(self) {
            return None;
        }
        Some(Monomial {
            exps: self
                .exps
                .iter()
                .zip(&other.exps)
                .map(|(a, b)| a - b)
                .collect(),
        })
    }

    pub fn lcm(&self, other: &Monomial) -> Monomial {
        Monomial {
            exps: self
                .exps
                .iter()
                .zip(&other.exps)
                .map(|(a, b)| *a.max(b))
                .collect(),
        }
    }

    /// Printable form, e.g. `x*y^2`; the empty string for the constant
    /// monomial.
    pub fn show(&self, names: &[&str]) -> String {
        let mut out = String::new();
        for (i, e) in self.exps.iter().enumerate() {
            if *e == 0 {
                continue;
            }
            if !out.is_empty() {
                out.push('*');
            }
            out.push_str(names[i]);
            if *e > 1 {
                let _ = write!(out, "^{e}");
            }
        }
        out
    }
}

/// The three standard monomial orders.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum MonomialOrder {
    /// Lexicographic.
    Lex,
    /// Graded lexicographic: total degree, then lex.
    GrLex,
    /// Graded reverse lexicographic: total degree, then the *rightmost*
    /// differing exponent, smaller winning.
    GrevLex,
}

impl MonomialOrder {
    pub fn cmp(&self, a: &Monomial, b: &Monomial) -> Ordering {
        match self {
            MonomialOrder::Lex => lex(a, b),
            MonomialOrder::GrLex => a
                .total_degree()
                .cmp(&b.total_degree())
                .then_with(|| lex(a, b)),
            MonomialOrder::GrevLex => a
                .total_degree()
                .cmp(&b.total_degree())
                .then_with(|| revlex(a, b)),
        }
    }
}

fn lex(a: &Monomial, b: &Monomial) -> Ordering {
    for (x, y) in a.exps.iter().zip(&b.exps) {
        match x.cmp(y) {
            Ordering::Equal => continue,
            other => return other,
        }
    }
    Ordering::Equal
}

fn revlex(a: &Monomial, b: &Monomial) -> Ordering {
    for (x, y) in a.exps.iter().zip(&b.exps).rev() {
        match x.cmp(y) {
            Ordering::Equal => continue,
            // The one with the smaller rightmost exponent is greater.
            other => return other.reverse(),
        }
    }
    Ordering::Equal
}

#[cfg(test)]
mod tests {
    use super::*;

    fn m(e: &[u32]) -> Monomial {
        Monomial::new(e.to_vec())
    }

    #[test]
    fn divisibility_and_lcm() {
        assert!(m(&[1, 0, 0]).divides(&m(&[2, 1, 0])));
        assert!(!m(&[0, 2, 0]).divides(&m(&[2, 1, 0])));
        assert_eq!(m(&[2, 1, 0]).div(&m(&[1, 0, 0])), Some(m(&[1, 1, 0])));
        assert_eq!(m(&[2, 1, 0]).lcm(&m(&[1, 0, 3])), m(&[2, 1, 3]));
    }

    #[test]
    fn lex_ignores_total_degree_and_the_graded_orders_do_not() {
        // x*y^2*z^3 (degree 6) vs x^3*y^2 (degree 5), with x > y > z.
        let a = m(&[1, 2, 3]);
        let b = m(&[3, 2, 0]);
        // Lex looks at the x exponent first and stops: 1 < 3.
        assert_eq!(MonomialOrder::Lex.cmp(&a, &b), Ordering::Less);
        // Grlex weighs total degree first: 6 > 5.
        assert_eq!(MonomialOrder::GrLex.cmp(&a, &b), Ordering::Greater);
    }

    #[test]
    fn grlex_and_grevlex_disagree_on_equal_degrees() {
        // x*z^2 vs y^3, both degree 3, with x > y > z.
        let a = m(&[1, 0, 2]);
        let b = m(&[0, 3, 0]);
        // Grlex breaks the degree tie with lex: x beats y.
        assert_eq!(MonomialOrder::GrLex.cmp(&a, &b), Ordering::Greater);
        // Grevlex breaks it on the rightmost differing exponent, where
        // the smaller one wins: y^3 uses no z at all, so it is greater.
        assert_eq!(MonomialOrder::GrevLex.cmp(&a, &b), Ordering::Less);
    }

    #[test]
    fn orders_are_compatible_with_multiplication() {
        let a = m(&[2, 0, 1]);
        let b = m(&[1, 1, 1]);
        let c = m(&[0, 3, 2]);
        for ord in [
            MonomialOrder::Lex,
            MonomialOrder::GrLex,
            MonomialOrder::GrevLex,
        ] {
            assert_eq!(ord.cmp(&a, &b), ord.cmp(&a.mul(&c), &b.mul(&c)));
        }
    }
}
