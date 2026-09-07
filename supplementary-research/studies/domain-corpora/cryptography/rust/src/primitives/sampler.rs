//! `Sampler`.
//!
//! **Vendored verbatim** from
//! `supplementary-research/studies/domain-corpora/algorithms/rust/src/primitives/control.rs` (`Sampler` section).
//!
//! **Cross-corpus framing note.** `Sampler` is the one primitive in the
//! six-primitive cryptography build set that is **asymmetric** to the
//! classical algorithms corpus: no algorithm in the 87-algorithm classical
//! corpus exercises `Sampler` —
//! classical algorithms-in-isolation don't need randomness. Cryptography
//! does: entropy source reads, DRBG output, rejection sampling (in
//! Dilithium-style signatures), Miller-Rabin witnesses for RSA
//! key-generation, RSA-PSS salt selection. The five-primitive overlap
//! (ResourceRegistry, TraversalEngine, ActuationPass, Reduction,
//! Bisection) plus Sampler-asymmetric-to-cryptography is the
//! substantive cross-corpus result of the algorithm corpus.

/// **Motivation.** Probabilistic selection from a distribution.
///
/// **Definition.** Deterministic-seeded selection of items
/// (a linear-congruential stream keeps reproducibility — the
/// cryptographic corpus tests require every run to produce the same
/// inputs).
///
/// **Invariant.** Distributional correctness over the seed stream.
///
/// **Note on cryptographic use.** The Sampler in this corpus is the
/// *test-input generator*, not a CSPRNG. Cryptographic compositions
/// that need entropy (RSA-PSS salt; Miller-Rabin witnesses) accept the
/// random bytes as an input parameter from the harness, which uses a
/// Sampler with a fixed test seed. No production code should use this
/// Sampler as a key/nonce source.
pub struct Sampler {
    state: u64,
}
impl Sampler {
    pub fn new(seed: u64) -> Self {
        Self { state: seed }
    }
    fn next_u64(&mut self) -> u64 {
        // LCG (Numerical Recipes constants) — reproducible.
        self.state = self
            .state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }
    pub fn pick_index(&mut self, n: usize) -> usize {
        if n == 0 {
            0
        } else {
            (self.next_u64() as usize) % n
        }
    }
    /// Produce a byte string of `len` deterministic-pseudorandom bytes.
    /// Used to generate test inputs (random keys, nonces, messages,
    /// salts) for the property-based test layer.
    pub fn bytes(&mut self, len: usize) -> Vec<u8> {
        let mut out = Vec::with_capacity(len);
        while out.len() < len {
            let word = self.next_u64();
            for shift in (0..64).step_by(8) {
                if out.len() < len {
                    out.push((word >> shift) as u8);
                }
            }
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn deterministic_for_a_given_seed() {
        let mut a = Sampler::new(0xDEADBEEF);
        let mut b = Sampler::new(0xDEADBEEF);
        assert_eq!(a.bytes(32), b.bytes(32));
    }
    #[test]
    fn pick_index_is_bounded() {
        let mut s = Sampler::new(42);
        for _ in 0..100 {
            assert!(s.pick_index(10) < 10);
        }
    }
}
