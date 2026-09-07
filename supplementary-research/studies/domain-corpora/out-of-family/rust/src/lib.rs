//! # Out-of-family evidence corpus
//!
//! Executable artifact for the adversarial out-of-family stress test.
//! The domains are the ones the connective census never touched: term
//! rewriting, computer algebra, and proof search.
//!
//! ## Authoring discipline
//!
//! 1. **Canonical algorithms only.** Each module implements the
//!    *published* algorithm, so its data structures and control flow are
//!    fixed by the literature rather than chosen by the author.
//! 2. **External anchoring.** Each algorithm is validated against
//!    third-party-checkable reference output plus independently
//!    verifiable structural properties (see `tests/`).
//! 3. **Faithful first, decomposed second.** These modules import no
//!    primitive realization and use no catalog vocabulary. The
//!    decomposition happens afterwards, over this code as written.
//!
//! ## Contents
//!
//! - [`rewriting`] — **Knuth-Bendix completion** (Knuth & Bendix
//!   1970; Huet 1981), with terms, unification, the lexicographic path
//!   order, rewriting and critical pairs.
//! - [`algebra`] — **Buchberger's algorithm** for Groebner bases
//!   (Buchberger 1965), with exact rationals, monomial orders and
//!   order-carrying multivariate polynomials.
//! - [`search`] — **The DPLL procedure** (Davis, Logemann &
//!   Loveland 1962) over CNF formulas.

pub mod algebra;
pub mod rewriting;
pub mod search;

pub use rewriting::completion::{complete, CompletionOutcome};
pub use rewriting::order::Precedence;
pub use rewriting::rewrite::Rule;
pub use rewriting::term::Term;

pub use algebra::buchberger::{groebner_basis, reduced_groebner_basis};
pub use algebra::monomial::{Monomial, MonomialOrder};
pub use algebra::poly::Poly;
pub use algebra::rational::Rat;

pub use search::cnf::{pigeonhole, Clause, Cnf, Lit, Model};
pub use search::dpll::{solve, SatOutcome};
