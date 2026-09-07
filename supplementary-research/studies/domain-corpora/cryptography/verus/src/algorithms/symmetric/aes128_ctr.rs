// AES-128-CTR (NIST SP 800-38A §6.5).
//
// AES-128-CTR instantiates block-to-stream-conversion on top of
// AES-128. For each block index i, the keystream
// block is AES-128(key, counter_i), where counter_i is the IV/counter
// block incremented i times (big-endian). The ciphertext is the
// per-byte XOR of plaintext and keystream.
//
// The chain shape is verified concretely: per-block keystream + XOR is
// captured by `aes128_ctr_keystream_block_spec` and a verified loop
// invariant. Counter increment is uninterp + external_body; validated
// extrinsically by NIST SP 800-38A Appendix F.5.1 KAT.
//
// TLAPS reference: BlockToStreamConversion_Proof.tla (312 obligations).
//
// Verification boundary: written contracts plus named external-body assumptions.

use crate::algorithms::symmetric::aes128::{
    aes128_encrypt_block, aes128_encrypt_block_spec, AES128_BLOCK_BYTES,
};
use vstd::prelude::*;

verus! {

// ── chain specs ────────────────────────────────────────────────

/// increment_be_counter_spec: 128-bit big-endian increment of a
/// 16-byte counter block. Uninterp.
pub uninterp spec fn increment_be_counter_spec(counter: Seq<u8>) -> Seq<u8>;

/// counter_at_spec(iv_counter, i): the counter block for the i-th
/// keystream block. Recursive over i; counter_at(iv, 0) = iv,
/// counter_at(iv, i) = increment(counter_at(iv, i-1)).
pub open spec fn counter_at_spec(iv_counter: Seq<u8>, i: int) -> Seq<u8>
    decreases i,
{
    if i <= 0 {
        iv_counter
    } else {
        increment_be_counter_spec(counter_at_spec(iv_counter, i - 1))
    }
}

/// keystream_block_at_spec(key, iv, i): the i-th 16-byte keystream
/// block — AES-128(key, counter_at(iv, i)).
pub open spec fn keystream_block_at_spec(key: Seq<u8>, iv: Seq<u8>, i: int) -> Seq<u8> {
    aes128_encrypt_block_spec(key, counter_at_spec(iv, i))
}

/// ciphertext_byte_at_spec(key, iv, plaintext, k): the k-th byte of
/// the output ciphertext.
pub open spec fn ciphertext_byte_at_spec(
    key: Seq<u8>,
    iv: Seq<u8>,
    plaintext: Seq<u8>,
    k: int,
) -> u8 {
    plaintext[k] ^ keystream_block_at_spec(key, iv, k / 16)[k % 16]
}

// ── External-body counter increment ────────────────────────────────

#[verifier::external_body]
pub fn increment_be_counter(counter: &mut [u8; 16])
    ensures final(counter)@ == increment_be_counter_spec(old(counter)@),
{
    let mut i: usize = 16;
    while i > 0 {
        i -= 1;
        counter[i] = counter[i].wrapping_add(1);
        if counter[i] != 0 { break; }
    }
}

// ── Verified block-to-stream encrypt ──────────────────────────

/// aes128_ctr_encrypt: chain. For each block, generate the
/// keystream block and XOR into the plaintext. Verified against
/// `ciphertext_byte_at_spec` for every output byte.
pub fn aes128_ctr_encrypt(
    key: &[u8; 16],
    iv_counter: &[u8; 16],
    plaintext: &[u8],
) -> (out: Vec<u8>)
    requires plaintext@.len() < 0x4000_0000u64,
    ensures
        out@.len() == plaintext@.len(),
        forall|k: int| 0 <= k < out@.len()
            ==> out@[k] == ciphertext_byte_at_spec(key@, iv_counter@, plaintext@, k),
{
    let n = plaintext.len();
    let mut out: Vec<u8> = Vec::with_capacity(n);
    let mut counter: [u8; 16] = *iv_counter;
    let mut b: usize = 0;
    let mut off: usize = 0;

    // Phase 1: full 16-byte blocks.
    while off + AES128_BLOCK_BYTES <= n
        invariant
            off <= n,
            off == b * AES128_BLOCK_BYTES,
            off + AES128_BLOCK_BYTES <= n + AES128_BLOCK_BYTES,
            n == plaintext@.len(),
            n < 0x4000_0000u64,
            counter@ == counter_at_spec(iv_counter@, b as int),
            out@.len() == off as int,
            forall|k: int| 0 <= k < out@.len()
                ==> out@[k] == ciphertext_byte_at_spec(key@, iv_counter@, plaintext@, k),
        decreases n - off,
    {
        let ks = aes128_encrypt_block(key, &counter);
        proof {
            assert(ks@ == keystream_block_at_spec(key@, iv_counter@, b as int));
        }
        let mut k: usize = 0;
        while k < AES128_BLOCK_BYTES
            invariant
                k <= AES128_BLOCK_BYTES,
                off == b * AES128_BLOCK_BYTES,
                off + AES128_BLOCK_BYTES <= n,
                n == plaintext@.len(),
                ks@ == keystream_block_at_spec(key@, iv_counter@, b as int),
                out@.len() == (off + k) as int,
                forall|m: int| 0 <= m < (off + k) as int
                    ==> out@[m] == ciphertext_byte_at_spec(key@, iv_counter@, plaintext@, m),
            decreases AES128_BLOCK_BYTES - k,
        {
            let kbyte = ks[k];
            assert(k < AES128_BLOCK_BYTES);
            assert(off + AES128_BLOCK_BYTES <= n);
            let abs_idx = off + k;
            assert(abs_idx < n);
            assert(abs_idx < plaintext@.len());
            proof {
                assert((abs_idx as int) / 16 == b as int);
                assert((abs_idx as int) % 16 == k as int);
                assert(kbyte == keystream_block_at_spec(key@, iv_counter@, b as int)[k as int]);
            }
            let pt_byte = plaintext[abs_idx];
            out.push(pt_byte ^ kbyte);
            k = k + 1;
        }
        increment_be_counter(&mut counter);
        off = off + AES128_BLOCK_BYTES;
        b = b + 1;
    }

    // Phase 2: final partial block (if any).
    if off < n {
        let ks = aes128_encrypt_block(key, &counter);
        proof {
            assert(ks@ == keystream_block_at_spec(key@, iv_counter@, b as int));
        }
        let mut k: usize = 0;
        let remaining = n - off;
        while k < remaining
            invariant
                k <= remaining,
                remaining == n - off,
                off == b * AES128_BLOCK_BYTES,
                off + remaining == n,
                remaining < AES128_BLOCK_BYTES,
                n == plaintext@.len(),
                ks@ == keystream_block_at_spec(key@, iv_counter@, b as int),
                out@.len() == (off + k) as int,
                forall|m: int| 0 <= m < (off + k) as int
                    ==> out@[m] == ciphertext_byte_at_spec(key@, iv_counter@, plaintext@, m),
            decreases remaining - k,
        {
            let kbyte = ks[k];
            assert(k < remaining);
            assert(off + remaining == n);
            let abs_idx = off + k;
            assert(abs_idx < n);
            assert(abs_idx < plaintext@.len());
            proof {
                assert((abs_idx as int) / 16 == b as int);
                assert((abs_idx as int) % 16 == k as int);
                assert(kbyte == keystream_block_at_spec(key@, iv_counter@, b as int)[k as int]);
            }
            let pt_byte = plaintext[abs_idx];
            out.push(pt_byte ^ kbyte);
            k = k + 1;
        }
    }
    out
}

}
