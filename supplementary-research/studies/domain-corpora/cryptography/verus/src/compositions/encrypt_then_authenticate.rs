// EncryptThenAuthenticate (AEAD).
//
// Three-phase AEAD: encrypt phase (block-to-stream), authenticate
// phase (polynomial-MAC over AAD || ciphertext), tag-derivation
// phase. The TLAPS proof at supplementary-research/studies/domain-corpora/cryptography/tla/compositions/
// EncryptThenAuthenticate_Proof.tla closes 424 obligations.
//
// For Verus, the AEAD composition is a function that produces
// (ciphertext, tag) from (key, nonce, aad, plaintext). The ciphertext
// is the encrypt_ctr output; the tag is the polynomial MAC over the
// (aad || ciphertext) sequence combined with a nonce-derived
// mixing constant.
//
// Verification boundary: written contracts plus named external-body assumptions.

use vstd::prelude::*;

verus! {

/// Concrete tag-mixing: XOR with a nonce-derived constant. The TLA+
/// spec uses TagMix as an abstract operator; it is instantiated as XOR.
pub open spec fn tag_mix_spec(auth_acc: u64, nonce: u64) -> u64 {
    auth_acc ^ nonce
}

pub fn tag_mix(auth_acc: u64, nonce: u64) -> (r: u64)
    ensures r == tag_mix_spec(auth_acc, nonce),
{
    auth_acc ^ nonce
}

/// AEAD's three-phase encrypt+auth: returns (ciphertext, tag).
///
/// Phase 1 (encrypt): produce ciphertext = plaintext XOR keystream
/// (concrete keystream: per-block wrapping arithmetic; in real AES-GCM
/// or ChaCha20-Poly1305 this is the block cipher).
/// Phase 2 (auth_aad): accumulate AAD through XOR fold.
/// Phase 3 (auth_ct): accumulate ciphertext through XOR fold.
/// Phase 4 (tag): apply tag_mix to the auth accumulator.
pub fn aead_encrypt(key: u64, nonce: u64, aad: &[u64], plaintext: &[u64])
    -> (out: (Vec<u64>, u64))
    requires aad@.len() as int + plaintext@.len() as int <= 1_000_000_000,
    ensures
        out.0@.len() == plaintext@.len() as int,
{
    // Encrypt phase: keystream = key XOR (counter mixed via wrapping mult)
    let mut ct: Vec<u64> = Vec::new();
    let n: usize = plaintext.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == plaintext@.len(),
            ct@.len() == i as int,
        decreases n - i,
    {
        let ks = key ^ (i as u64).wrapping_mul(0x9E3779B97F4A7C15u64);
        ct.push(plaintext[i] ^ ks);
        i = i + 1;
    }

    // Auth phase: XOR all AAD entries and ciphertext entries together
    // into an accumulator (a degenerate polynomial-MAC with r = 1 and
    // simple XOR aggregation; full polynomial-MAC at algorithm
    // instantiation).
    let mut acc: u64 = 0;
    let mut j: usize = 0;
    let aad_len: usize = aad.len();
    while j < aad_len
        invariant
            j <= aad_len,
            aad_len == aad@.len(),
        decreases aad_len - j,
    {
        acc = acc ^ aad[j];
        j = j + 1;
    }
    let mut k: usize = 0;
    while k < n
        invariant
            k <= n,
            n == ct@.len(),
        decreases n - k,
    {
        acc = acc ^ ct[k];
        k = k + 1;
    }

    // Tag phase.
    let tag = tag_mix(acc, nonce);
    (ct, tag)
}

}
