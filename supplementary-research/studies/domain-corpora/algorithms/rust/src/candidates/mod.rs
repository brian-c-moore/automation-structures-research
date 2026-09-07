//! Candidate primitives: mechanisms that recur across the corpus and
//! carry a governance invariant, but are held apart from the canonical
//! set. Their formal treatment is the TLA+ track's Bisection and
//! EquivalenceClass modules plus the paired `*Decomposed`
//! irreducibility specs.

pub mod bisection;
pub mod equivalence_class;

pub use bisection::Bisection;
pub use equivalence_class::EquivalenceClass;
