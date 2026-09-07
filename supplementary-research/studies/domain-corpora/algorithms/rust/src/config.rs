//! The per-algorithm corpus manifest.
//!
//! The code registry ([`CorpusEntry`] values pushed by each
//! `compositions` phase module) is the single executable registry.
//! [`write_manifest`] emits a human-inspectable `tests.toml` mirror so
//! the corpus can be read without running it.

use crate::value::Value;
use serde::Serialize;

/// One corpus algorithm: its composition (primitives-only), its Python
/// oracle key, its equivalence relation, and its three-axis metadata.
#[derive(Clone)]
pub struct CorpusEntry {
    pub name: &'static str,
    pub category: &'static str,
    pub phase: u8,
    /// Structural ordering: Linear / Tree / DAG / Graph-with-cycles.
    pub ordering: &'static str,
    /// Composition shape in the algorithm corpus vocabulary.
    pub primitives: &'static str,
    /// The composition, built ONLY from `primitives`/`candidates`.
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

#[derive(Serialize)]
struct ManifestRow {
    name: &'static str,
    category: &'static str,
    phase: u8,
    ordering: &'static str,
    primitives: &'static str,
    oracle: &'static str,
    equiv: String,
}

#[derive(Serialize)]
struct Manifest {
    algorithm: Vec<ManifestRow>,
}

/// Serialize the registry metadata to `tests.toml` at the crate root.
pub fn write_manifest() -> std::io::Result<()> {
    let rows: Vec<ManifestRow> = registry()
        .iter()
        .map(|e| ManifestRow {
            name: e.name,
            category: e.category,
            phase: e.phase,
            ordering: e.ordering,
            primitives: e.primitives,
            oracle: e.oracle,
            equiv: format!("{:?}", e.equiv),
        })
        .collect();
    let toml = toml::to_string(&Manifest { algorithm: rows }).unwrap();
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests.toml");
    std::fs::write(path, toml)
}
