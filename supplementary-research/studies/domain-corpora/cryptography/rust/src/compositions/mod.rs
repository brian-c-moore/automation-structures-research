//! The seven-algorithm executable cryptography subset. Each algorithm
//! is built **only** from [`crate::primitives`] and [`crate::content`]
//! - no direct cryptographic-library calls. No algorithm
//! re-implements primitive logic.
//!
//! The exact subset is SHA-256, SHA-3-256, BLAKE3, ChaCha20,
//! HMAC-SHA-256, HKDF-SHA-256, and PBKDF2-HMAC-SHA-256. Algorithms
//! outside this list receive no executable evidence from this crate.

use crate::config::CorpusEntry;
use crate::value::Value;

pub mod hashes;
pub mod kdf;
pub mod mac;
pub mod symmetric;

/// Concatenate every implemented family's entries.
pub fn registry() -> Vec<CorpusEntry> {
    let mut r = Vec::new();
    hashes::add(&mut r);
    symmetric::add(&mut r);
    mac::add(&mut r);
    kdf::add(&mut r);
    r
}

/// Shared input generation for the property-based test layer.
/// Cryptographic inputs are random byte strings of varying length;
/// the Sampler is seeded deterministically so runs are reproducible.
pub mod gen {
    use crate::primitives::Sampler;
    use crate::value::Value;

    /// Deterministic random byte messages: 50 messages of length
    /// 0..=128 bytes. The length distribution emphasizes block-boundary
    /// edge cases (length-around-block, length-around-block+1, etc.).
    pub fn random_byte_messages() -> Vec<Value> {
        let mut s = Sampler::new(0xDEADBEEF);
        let mut out = Vec::with_capacity(60);
        // Curated edge-case lengths.
        for len in [0usize, 1, 55, 56, 63, 64, 65, 119, 120, 127, 128] {
            out.push(Value::Bytes(s.bytes(len)));
        }
        // Plus 50 random-length messages.
        for _ in 0..50 {
            let len = s.pick_index(129);
            out.push(Value::Bytes(s.bytes(len)));
        }
        out
    }
}

/// Shared per-phase helper for constructing registry entries.
#[allow(clippy::too_many_arguments)]
pub fn entry(
    r: &mut Vec<CorpusEntry>,
    name: &'static str,
    category: &'static str,
    phase: u8,
    ordering: &'static str,
    primitives: &'static str,
    compose: fn(Value) -> Value,
    oracle: &'static str,
    equiv: crate::equivalence::Equiv,
    gen_inputs: fn() -> Vec<Value>,
) {
    r.push(CorpusEntry {
        name,
        category,
        phase,
        ordering,
        primitives,
        compose,
        oracle,
        equiv,
        gen_inputs,
    });
}
