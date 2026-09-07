//! Multivariate polynomials over the rationals, **kept in monomial
//! order**.
//!
//! The representation is the classical one: a list of (monomial,
//! coefficient) terms held in strictly descending order under the
//! polynomial's monomial order, with no zero coefficients. Every later
//! pass consumes that order — the leading term is `terms[0]`, division
//! cancels leading terms, and the S-polynomial is built from two leading
//! terms. Addition is a merge of two ordered term lists.

use super::monomial::{Monomial, MonomialOrder};
use super::rational::Rat;
use std::cmp::Ordering;

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Poly {
    pub nvars: usize,
    pub order: MonomialOrder,
    /// Strictly descending under `order`; no zero coefficients.
    pub terms: Vec<(Monomial, Rat)>,
}

impl Poly {
    pub fn zero(nvars: usize, order: MonomialOrder) -> Poly {
        Poly {
            nvars,
            order,
            terms: Vec::new(),
        }
    }

    /// Build from arbitrary terms: put them in order, combine like
    /// monomials, drop zero coefficients.
    pub fn from_terms(nvars: usize, order: MonomialOrder, mut terms: Vec<(Monomial, Rat)>) -> Poly {
        terms.sort_by(|a, b| order.cmp(&b.0, &a.0));
        let mut out: Vec<(Monomial, Rat)> = Vec::new();
        for (m, c) in terms {
            match out.last_mut() {
                Some((lm, lc)) if *lm == m => *lc = *lc + c,
                _ => out.push((m, c)),
            }
        }
        out.retain(|(_, c)| !c.is_zero());
        Poly {
            nvars,
            order,
            terms: out,
        }
    }

    /// A single term.
    pub fn term(nvars: usize, order: MonomialOrder, m: Monomial, c: Rat) -> Poly {
        if c.is_zero() {
            Poly::zero(nvars, order)
        } else {
            Poly {
                nvars,
                order,
                terms: vec![(m, c)],
            }
        }
    }

    pub fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    pub fn leading(&self) -> Option<&(Monomial, Rat)> {
        self.terms.first()
    }

    pub fn lm(&self) -> Option<&Monomial> {
        self.terms.first().map(|(m, _)| m)
    }

    pub fn lc(&self) -> Option<Rat> {
        self.terms.first().map(|(_, c)| *c)
    }

    /// Merge of two ordered term lists.
    pub fn add(&self, other: &Poly) -> Poly {
        debug_assert_eq!(self.order, other.order);
        let mut out: Vec<(Monomial, Rat)> = Vec::new();
        let mut i = 0;
        let mut j = 0;
        while i < self.terms.len() && j < other.terms.len() {
            let (ref am, ac) = self.terms[i];
            let (ref bm, bc) = other.terms[j];
            match self.order.cmp(am, bm) {
                Ordering::Greater => {
                    out.push((am.clone(), ac));
                    i += 1;
                }
                Ordering::Less => {
                    out.push((bm.clone(), bc));
                    j += 1;
                }
                Ordering::Equal => {
                    let c = ac + bc;
                    if !c.is_zero() {
                        out.push((am.clone(), c));
                    }
                    i += 1;
                    j += 1;
                }
            }
        }
        out.extend_from_slice(&self.terms[i..]);
        out.extend_from_slice(&other.terms[j..]);
        Poly {
            nvars: self.nvars,
            order: self.order,
            terms: out,
        }
    }

    pub fn neg(&self) -> Poly {
        Poly {
            nvars: self.nvars,
            order: self.order,
            terms: self.terms.iter().map(|(m, c)| (m.clone(), -*c)).collect(),
        }
    }

    pub fn sub(&self, other: &Poly) -> Poly {
        self.add(&other.neg())
    }

    /// Multiply by a single term. A monomial order is compatible with
    /// multiplication, so the result is already in order.
    pub fn mul_term(&self, m: &Monomial, c: Rat) -> Poly {
        if c.is_zero() {
            return Poly::zero(self.nvars, self.order);
        }
        Poly {
            nvars: self.nvars,
            order: self.order,
            terms: self
                .terms
                .iter()
                .map(|(tm, tc)| (tm.mul(m), *tc * c))
                .collect(),
        }
    }

    /// Scale so the leading coefficient is one.
    pub fn monic(&self) -> Poly {
        match self.lc() {
            None => self.clone(),
            Some(c) => self.mul_term(&Monomial::one(self.nvars), c.inv()),
        }
    }

    pub fn show(&self, names: &[&str]) -> String {
        if self.is_zero() {
            return "0".to_string();
        }
        let mut s = String::new();
        for (k, (m, c)) in self.terms.iter().enumerate() {
            let neg = c.is_negative();
            let mag = if neg { -*c } else { *c };
            if k == 0 {
                if neg {
                    s.push('-');
                }
            } else {
                s.push_str(if neg { " - " } else { " + " });
            }
            let ms = m.show(names);
            if mag != Rat::ONE || ms.is_empty() {
                s.push_str(&mag.to_string());
                if !ms.is_empty() {
                    s.push('*');
                }
            }
            s.push_str(&ms);
        }
        s
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn m(e: &[u32]) -> Monomial {
        Monomial::new(e.to_vec())
    }

    fn p(terms: Vec<(&[u32], i128)>) -> Poly {
        Poly::from_terms(
            3,
            MonomialOrder::Lex,
            terms
                .into_iter()
                .map(|(e, c)| (m(e), Rat::int(c)))
                .collect(),
        )
    }

    const XYZ: [&str; 3] = ["x", "y", "z"];

    #[test]
    fn construction_orders_combines_and_prunes() {
        // z + x + y + z, entered out of order, with a cancelling pair.
        let f = p(vec![
            (&[0, 0, 1], 1),
            (&[1, 0, 0], 1),
            (&[0, 1, 0], 1),
            (&[0, 0, 1], -1),
        ]);
        assert_eq!(f.show(&XYZ), "x + y");
        assert_eq!(f.lm(), Some(&m(&[1, 0, 0])));
    }

    #[test]
    fn addition_merges_and_cancels() {
        let a = p(vec![(&[1, 0, 0], 1), (&[0, 1, 0], 1)]);
        let b = p(vec![(&[0, 1, 0], -1), (&[0, 0, 1], 3)]);
        assert_eq!(a.add(&b).show(&XYZ), "x + 3*z");
        assert!(a.sub(&a).is_zero());
    }

    #[test]
    fn term_multiplication_preserves_order() {
        let f = p(vec![(&[1, 0, 0], 1), (&[0, 2, 0], 1), (&[0, 0, 3], 1)]);
        let g = f.mul_term(&m(&[0, 1, 1]), Rat::int(2));
        let mut sorted = g.terms.clone();
        sorted.sort_by(|a, b| g.order.cmp(&b.0, &a.0));
        assert_eq!(g.terms, sorted);
        assert_eq!(g.show(&XYZ), "2*x*y*z + 2*y^3*z + 2*y*z^4");
    }

    #[test]
    fn monic_normalizes_the_leading_coefficient() {
        let f = p(vec![(&[1, 0, 0], 3), (&[0, 1, 0], 6)]);
        assert_eq!(f.monic().show(&XYZ), "x + 2*y");
    }
}
