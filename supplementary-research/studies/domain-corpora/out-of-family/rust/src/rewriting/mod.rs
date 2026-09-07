//! **Term rewriting.** Knuth-Bendix completion and the machinery it
//! needs: first-order terms, unification, the lexicographic path order,
//! rewriting, and critical pairs.

pub mod completion;
pub mod critical_pairs;
pub mod order;
pub mod rewrite;
pub mod term;
pub mod unify;
