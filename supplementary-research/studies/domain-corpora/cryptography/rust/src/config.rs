//! The per-algorithm corpus registry.
//!
//! The code registry ([`CorpusEntry`] values pushed by each
//! implemented composition family) is the executable source of truth.
//! The checked-in `tests.toml` lists the same exact seven algorithms for
//! inspection without executing the crate.

use crate::value::Value;

/// One corpus algorithm: its composition (primitives-only), its Python
/// oracle key, its equivalence relation, and its three-axis metadata.
#[derive(Clone)]
pub struct CorpusEntry {
    pub name: &'static str,
    pub category: &'static str,
    pub phase: u8,
    /// Structural ordering: Linear / Tree / DAG / Graph-with-cycles.
    pub ordering: &'static str,
    /// Composition shape in the algorithm corpus vocabulary (recorded, teaching).
    pub primitives: &'static str,
    /// The composition, built ONLY from `primitives`/`content`. No
    /// direct cryptographic-library calls: the composition is assembled
    /// from the six primitives plus content.
    pub compose: fn(Value) -> Value,
    /// Dispatch key into `python/oracles.py`.
    pub oracle: &'static str,
    pub equiv: crate::equivalence::Equiv,
    /// Curated and deterministic property-based inputs for the corpus.
    pub gen_inputs: fn() -> Vec<Value>,
}

pub type Registry = Vec<CorpusEntry>;

/// Build the full registry from every phase module at one aggregation point.
pub fn registry() -> Registry {
    crate::compositions::registry()
}
