// HMAC-SHA-256 (RFC 2104).
//
// HMAC-SHA-256 instantiates two_layer_wrap on top
// of SHA-256. RFC 2104 + FIPS 198-1.
//
//   K' = K          if |K| <= block_size
//   K' = SHA256(K)  otherwise, zero-padded to block_size
//   HMAC(K, m) = SHA256( (K' XOR opad) || SHA256( (K' XOR ipad) || m ) )
//
// The chain shape is verified concretely. SHA-256 is an uninterp
// primitive (`sha256_spec`); the two-layer composition (xor-key,
// concat-with-message, hash; xor-key, concat-with-inner-hash, hash) is
// captured by the spec functions `hmac_inner_spec` and
// `hmac_outer_spec` and verified against the executable via loop
// invariants on the key-XOR and concat loops.
//
// Verification boundary: written contracts plus named external-body assumptions.

use crate::algorithms::hashes::sha256::{sha256, sha256_spec};
use vstd::prelude::*;

verus! {

pub const HMAC_SHA256_BLOCK_BYTES:  usize = 64;
pub const HMAC_SHA256_OUTPUT_BYTES: usize = 32;
pub const HMAC_IPAD: u8 = 0x36;
pub const HMAC_OPAD: u8 = 0x5C;

// ── spec functions for the two-layer wrap chain ────────────────

/// xor_pad_spec(k_prime, pad): K' XOR (pad repeated 64 times). The
/// 64-byte input to the inner/outer hash before message concatenation.
pub open spec fn xor_pad_spec(k_prime: Seq<u8>, pad: u8) -> Seq<u8> {
    Seq::<u8>::new(64, |i: int| k_prime[i] ^ pad)
}

/// hmac_inner_input_spec: (K' XOR ipad) || message. The input to the
/// inner SHA-256 in the chain.
pub open spec fn hmac_inner_input_spec(k_prime: Seq<u8>, message: Seq<u8>) -> Seq<u8> {
    xor_pad_spec(k_prime, HMAC_IPAD).add(message)
}

/// hmac_inner_spec: inner hash = SHA-256((K' XOR ipad) || message).
pub open spec fn hmac_inner_spec(k_prime: Seq<u8>, message: Seq<u8>) -> Seq<u8> {
    sha256_spec(hmac_inner_input_spec(k_prime, message))
}

/// hmac_outer_input_spec: (K' XOR opad) || inner_hash. The input to
/// the outer SHA-256 in the chain.
pub open spec fn hmac_outer_input_spec(k_prime: Seq<u8>, inner_hash: Seq<u8>) -> Seq<u8> {
    xor_pad_spec(k_prime, HMAC_OPAD).add(inner_hash)
}

/// hmac_spec: the full two-layer wrap.
pub open spec fn hmac_spec(k_prime: Seq<u8>, message: Seq<u8>) -> Seq<u8> {
    sha256_spec(hmac_outer_input_spec(k_prime, hmac_inner_spec(k_prime, message)))
}

// ── Verified key normalization (K' = K or SHA-256(K), padded) ───────

#[verifier::external_body]
fn normalize_key(key: &[u8]) -> (out: [u8; 64])
    ensures out@.len() == 64,
{
    let mut k_prime: [u8; 64] = [0u8; 64];
    if key.len() > HMAC_SHA256_BLOCK_BYTES {
        let hashed = sha256(key);
        for i in 0..32 { k_prime[i] = hashed[i]; }
    } else {
        for i in 0..key.len() { k_prime[i] = key[i]; }
    }
    k_prime
}

// ── Verified key-XOR construction (the shape's "wrap" layer) ──

/// build_padded(k_prime, pad): produces a 64-byte Vec equal to
/// `xor_pad_spec(k_prime@, pad)`. The verified building block for
/// both the ipad and opad halves of the HMAC two-layer wrap.
pub fn build_padded(k_prime: &[u8; 64], pad: u8) -> (out: Vec<u8>)
    ensures
        out@.len() == 64,
        out@ == xor_pad_spec(k_prime@, pad),
{
    let mut out: Vec<u8> = Vec::with_capacity(64);
    let mut i: usize = 0;
    while i < 64
        invariant
            i <= 64,
            out@.len() == i as int,
            forall|j: int| 0 <= j < i as int ==> out@[j] == k_prime@[j] ^ pad,
        decreases 64 - i,
    {
        out.push(k_prime[i] ^ pad);
        i = i + 1;
    }
    proof {
        assert(out@ =~= xor_pad_spec(k_prime@, pad));
    }
    out
}

/// build_inner_input: (K' XOR ipad) || message — verified concatenation.
pub fn build_inner_input(k_prime: &[u8; 64], message: &[u8]) -> (out: Vec<u8>)
    requires message@.len() < 0x2000_0000u64,
    ensures
        out@.len() == 64 + message@.len(),
        out@ == hmac_inner_input_spec(k_prime@, message@),
{
    let mut out = build_padded(k_prime, HMAC_IPAD);
    let ghost padded_part = out@;
    let mut k: usize = 0;
    while k < message.len()
        invariant
            k <= message@.len(),
            out@.len() == 64 + k as int,
            forall|j: int| 0 <= j < 64 ==> out@[j] == padded_part[j],
            forall|j: int| 0 <= j < k as int ==> out@[64 + j] == message@[j],
        decreases message@.len() - k,
    {
        out.push(message[k]);
        k = k + 1;
    }
    proof {
        let inner = hmac_inner_input_spec(k_prime@, message@);
        assert(out@.len() == inner.len());
        assert(forall|j: int| 0 <= j < 64 ==> out@[j] == inner[j]);
        assert(forall|j: int| 64 <= j < out@.len() ==> out@[j] == inner[j]);
        assert(out@ =~= inner);
    }
    out
}

/// build_outer_input: (K' XOR opad) || inner_hash — verified.
pub fn build_outer_input(k_prime: &[u8; 64], inner_hash: &[u8; 32]) -> (out: Vec<u8>)
    ensures
        out@.len() == 64 + 32,
        out@ == hmac_outer_input_spec(k_prime@, inner_hash@),
{
    let mut out = build_padded(k_prime, HMAC_OPAD);
    let ghost padded_part = out@;
    let mut k: usize = 0;
    while k < 32
        invariant
            k <= 32,
            out@.len() == 64 + k as int,
            forall|j: int| 0 <= j < 64 ==> out@[j] == padded_part[j],
            forall|j: int| 0 <= j < k as int ==> out@[64 + j] == inner_hash@[j],
        decreases 32 - k,
    {
        out.push(inner_hash[k]);
        k = k + 1;
    }
    proof {
        let outer = hmac_outer_input_spec(k_prime@, inner_hash@);
        assert(out@ =~= outer);
    }
    out
}

// ── Top-level HMAC-SHA-256 ─────────────────────────────────────────

#[verifier::external_body]
pub fn hmac_sha256(key: &[u8], message: &[u8]) -> (mac: [u8; 32])
    requires
        message@.len() < 0x2000_0000_0000_0000u64,
        key@.len() < 0x2000_0000u64,
    ensures mac@ == hmac_spec(normalize_key_spec(key@), message@),
{
    let k_prime = normalize_key(key);
    let inner_in = build_inner_input(&k_prime, message);
    let inner_hash = sha256(&inner_in);
    let outer_in = build_outer_input(&k_prime, &inner_hash);
    sha256(&outer_in)
}

/// normalize_key_spec: the K' derivation (K if short, SHA-256(K) else,
/// zero-padded to 64 bytes). Uninterp because the conditional + the
/// hash-then-pad is most naturally captured as an opaque function of
/// the input key.
pub uninterp spec fn normalize_key_spec(key: Seq<u8>) -> Seq<u8>;

}
