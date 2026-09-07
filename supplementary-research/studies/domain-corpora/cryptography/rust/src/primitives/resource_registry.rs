//! `ResourceRegistry<K, V>`.
//!
//! **Vendored verbatim** from
//! `supplementary-research/studies/domain-corpora/algorithms/rust/src/primitives/data.rs` (`ResourceRegistry` section).
//! The same primitive that supports classical DP's memoization table
//! also supports cryptographic state registers, lookup tables (S-boxes,
//! round constants), derived key schedules, working buffers in bignum
//! routines, precomputed power tables, and DRBG state — that IS the
//! point of cross-domain transfer.

use std::collections::HashMap;
use std::hash::Hash;

/// **Motivation.** The most common operation in computation is "look up
/// a value by a key": hash maps, symbol tables, caches, memo tables,
/// visited sets, adjacency lists.
///
/// **Definition.** A typed key→value mapping with `insert`, `lookup`,
/// `delete`.
///
/// **Invariant.** Functional consistency: `lookup(k)` returns the most
/// recently inserted value for `k`, or `None` after delete / no insert.
///
/// **Recognition in cryptography.** Internal state of an iterative
/// transformation (SHA-256's eight working variables; AES's 4×4 state
/// matrix; ChaCha20's sixteen-word state; Keccak's twenty-five lanes).
/// Fixed lookup tables (AES's S-box; SHA-256's round constants;
/// ChaCha20's initial constants; Keccak's round constants and rotation
/// offsets). Derived key schedules (AES's eleven round keys; RSA's
/// Montgomery-form constants; Ed25519's clamped scalar). Working
/// buffers in bignum routines, precomputed power tables, DRBG state.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct ResourceRegistry<K: Eq + Hash + Clone, V: Clone> {
    map: HashMap<K, V>,
}

impl<K: Eq + Hash + Clone, V: Clone> ResourceRegistry<K, V> {
    pub fn new() -> Self {
        Self {
            map: HashMap::new(),
        }
    }
    pub fn insert(&mut self, key: K, value: V) {
        self.map.insert(key, value);
    }
    pub fn lookup(&self, key: &K) -> Option<&V> {
        self.map.get(key)
    }
    pub fn contains(&self, key: &K) -> bool {
        self.map.contains_key(key)
    }
    pub fn delete(&mut self, key: &K) -> Option<V> {
        self.map.remove(key)
    }
    pub fn len(&self) -> usize {
        self.map.len()
    }
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }
    pub fn entry_or(&mut self, key: K, default: V) -> &mut V {
        self.map.entry(key).or_insert(default)
    }
    pub fn values(&self) -> impl Iterator<Item = &V> {
        self.map.values()
    }
    pub fn keys(&self) -> impl Iterator<Item = &K> {
        self.map.keys()
    }
    // Functional consistency is enforced by the HashMap representation:
    // there is exactly one current value per key. No runtime predicate is
    // exported for that representation guarantee.
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn registry_functional_consistency() {
        let mut r: ResourceRegistry<i32, i32> = ResourceRegistry::new();
        r.insert(1, 10);
        r.insert(1, 20);
        assert_eq!(r.lookup(&1), Some(&20));
    }
}
