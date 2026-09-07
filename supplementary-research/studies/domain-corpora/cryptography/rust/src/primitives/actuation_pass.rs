//! `ActuationPass`.
//!
//! **Vendored verbatim** from
//! `supplementary-research/studies/domain-corpora/algorithms/rust/src/primitives/control.rs` (`ActuationPass` section).
//! In cryptography: per-round transformations (SHA-256 round function;
//! AES round combining SubBytes/ShiftRows/MixColumns/AddRoundKey;
//! ChaCha20 quarter-round; SHA-3's θ ρ π χ ι); per-block compressions
//! (BLAKE3's chunk compression; Poly1305's accumulator update);
//! scalar-multiplication step operations (point doubling, ladder steps,
//! modular squaring); per-limb bignum operations; dedicated CPU
//! instructions (aesenc, sha256rnds2, pclmulqdq treated as single
//! ActuationPasses).

/// **Motivation.** Apply a side-effecting operation to a determined set
/// of items — the "execute / apply / commit / write" step.
///
/// **Definition.** Map a per-item side-effecting op over exactly the
/// given items: no double-actuation, no skips.
///
/// **Invariant.** Actuation scope = exactly the supplied items.
pub struct ActuationPass;
impl ActuationPass {
    pub fn apply<T, F: FnMut(&mut T)>(items: &mut [T], mut f: F) {
        for it in items.iter_mut() {
            f(it);
        }
    }
    pub fn apply_each<T, F: FnMut(T)>(items: impl IntoIterator<Item = T>, mut f: F) {
        for it in items {
            f(it);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn applies_to_every_item_exactly_once() {
        let mut v = vec![0u32; 5];
        ActuationPass::apply(&mut v, |x| *x += 1);
        assert_eq!(v, vec![1, 1, 1, 1, 1]);
    }
}
