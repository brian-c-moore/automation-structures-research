//! `Reduction`.
//!
//! **Vendored verbatim** from
//! `supplementary-research/studies/domain-corpora/algorithms/rust/src/primitives/control.rs` (`Reduction` section).
//! XOR is the dominant Reduction operator in cryptography (AES's
//! AddRoundKey; SHA-3's absorb step; ChaCha20's keystream application;
//! HMAC's ipad/opad; PBKDF2's U-chain combination; CTR-mode keystream
//! application). Modular addition (SHA-256, ChaCha20 round functions),
//! carry-propagating addition (bignum arithmetic), polynomial addition
//! (GHASH, Poly1305) are the other instances.

/// **Motivation.** Collapse a stream of N values to one summary.
///
/// **Definition.** Fold under an associative binary operator with an
/// identity.
///
/// **Invariant.** Associativity: grouping does not change the result —
/// so a sequential fold and a parallel tree-reduce agree.
///
/// **Recognition in cryptography.** Universal in the form of XOR;
/// also modular addition, carry-propagating bignum addition, finite-field
/// polynomial addition.
pub struct Reduction;
impl Reduction {
    pub fn reduce<T, I, F>(iter: I, identity: T, op: F) -> T
    where
        I: IntoIterator<Item = T>,
        F: Fn(T, T) -> T,
    {
        iter.into_iter().fold(identity, |acc, x| op(acc, x))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn reduction_is_associative_for_sum() {
        let v = vec![1, 2, 3, 4, 5];
        let left = Reduction::reduce(v.clone(), 0, |a, b| a + b);
        let split: i32 = {
            let (l, r) = v.split_at(2);
            Reduction::reduce(l.to_vec(), 0, |a, b| a + b)
                + Reduction::reduce(r.to_vec(), 0, |a, b| a + b)
        };
        assert_eq!(left, split);
    }
    #[test]
    fn reduction_is_associative_for_xor() {
        let v: Vec<u32> = vec![0xDEADBEEF, 0xCAFEBABE, 0xF00DD00D, 0x12345678];
        let left = Reduction::reduce(v.clone(), 0u32, |a, b| a ^ b);
        let split: u32 = {
            let (l, r) = v.split_at(2);
            Reduction::reduce(l.to_vec(), 0u32, |a, b| a ^ b)
                ^ Reduction::reduce(r.to_vec(), 0u32, |a, b| a ^ b)
        };
        assert_eq!(left, split);
    }
}
