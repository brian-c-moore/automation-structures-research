// AES-128-GCM (NIST SP 800-38D).
//
// AES-128-GCM instantiates encrypt_then_authenticate, composing
// block-to-stream (GCTR) on top of AES-128 with a polynomial MAC over
// GF(2^128) (GHASH).
//
//   H   = AES-128(key, 0^128)         // hash subkey
//   J0  = IV || 0^31 || 1              // initial counter (96-bit IV)
//   CT  = GCTR(key, J0+1, plaintext)  // chain over 32-bit counter
//   GH  = GHASH(H, AAD || pad || CT || pad || len(AAD)*8 || len(CT)*8)
//                                      // Horner over GF(2^128)
//   tag = AES-128(key, J0) XOR GH
//
// The GCTR and GHASH chains are both verified concretely. The
// GF(2^128) bit-level multiplication is external_body; the AES block
// cipher is consumed via the verified `aes128_encrypt_block_spec`.
//
// TLAPS reference: EncryptThenAuthenticate_Proof.tla (424 obligations)
// + BlockToStreamConversion_Proof.tla (312 obligations) +
// PolynomialMacHornerForm_Proof.tla (387 obligations).
//
// Verification boundary: written contracts plus named external-body assumptions.

use crate::algorithms::symmetric::aes128::{
    aes128_encrypt_block, aes128_encrypt_block_spec, AES128_BLOCK_BYTES,
};
use vstd::prelude::*;

verus! {

/// aes128_gcm_encrypt_spec: AEAD encryption as a deterministic
/// function. Uninterp abstraction at the top level; the composition is
/// the structural target.
pub uninterp spec fn aes128_gcm_encrypt_spec(
    key: Seq<u8>, iv: Seq<u8>, aad: Seq<u8>, plaintext: Seq<u8>,
) -> (Seq<u8>, Seq<u8>);

// ── GCTR chain specs (32-bit counter increment per NIST §6.5) ──

/// gctr_inc32_spec: GCTR increment — increment only the last 32 bits
/// of the 16-byte counter block. Uninterp; concrete impl in ext_body.
pub uninterp spec fn gctr_inc32_spec(counter: Seq<u8>) -> Seq<u8>;

/// gctr_counter_at_spec(j0, i): the counter block for the i-th GCTR
/// keystream block. counter(j0, 0) = inc32(j0); counter(j0, i) =
/// inc32(counter(j0, i-1)). (CTR for GCM starts at J0 + 1.)
pub open spec fn gctr_counter_at_spec(j0: Seq<u8>, i: int) -> Seq<u8>
    decreases i,
{
    if i <= 0 {
        gctr_inc32_spec(j0)
    } else {
        gctr_inc32_spec(gctr_counter_at_spec(j0, i - 1))
    }
}

/// gctr_keystream_block_at_spec(key, j0, i): the i-th 16-byte GCTR
/// keystream block.
pub open spec fn gctr_keystream_block_at_spec(key: Seq<u8>, j0: Seq<u8>, i: int) -> Seq<u8> {
    aes128_encrypt_block_spec(key, gctr_counter_at_spec(j0, i))
}

/// gctr_ciphertext_byte_at_spec(key, j0, plaintext, k): the k-th byte
/// of the GCTR ciphertext.
pub open spec fn gctr_ciphertext_byte_at_spec(
    key: Seq<u8>, j0: Seq<u8>, plaintext: Seq<u8>, k: int,
) -> u8 {
    plaintext[k] ^ gctr_keystream_block_at_spec(key, j0, k / 16)[k % 16]
}

// ── GHASH chain specs ──────────────────────────────────────────

/// ghash_mul_spec: multiplication in GF(2^128) with the standard
/// reduction polynomial x^128 + x^7 + x^2 + x + 1. Uninterp.
pub uninterp spec fn ghash_mul_spec(a: Seq<u8>, b: Seq<u8>) -> Seq<u8>;

/// ghash_xor_spec(a, b): per-byte XOR of two 16-byte sequences.
pub open spec fn ghash_xor_spec(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> {
    Seq::<u8>::new(16, |i: int| a[i] ^ b[i])
}

/// ghash_zero_spec: the GHASH initial state (16 zero bytes).
pub open spec fn ghash_zero_spec() -> Seq<u8> {
    Seq::<u8>::new(16, |_i: int| 0u8)
}

/// take_block_spec(data, off): the 16-byte block at offset `off`.
pub open spec fn take_block_spec(data: Seq<u8>, off: int) -> Seq<u8> {
    Seq::<u8>::new(16, |i: int| data[off + i])
}

/// ghash_at_spec(h, data, n): GHASH accumulator after the first n
/// 16-byte blocks of `data`. Recursive; mirrors Horner.
pub open spec fn ghash_at_spec(h: Seq<u8>, data: Seq<u8>, n: int) -> Seq<u8>
    decreases n,
{
    if n <= 0 {
        ghash_zero_spec()
    } else {
        let prev = ghash_at_spec(h, data, n - 1);
        let block = take_block_spec(data, (n - 1) * 16);
        ghash_mul_spec(ghash_xor_spec(prev, block), h)
    }
}

// ── External-body field operations + counter increment ─────────────

#[verifier::external_body]
pub fn ghash_mul(x: &[u8; 16], y: &[u8; 16]) -> (out: [u8; 16])
    ensures out@ == ghash_mul_spec(x@, y@),
{
    let mut z: [u8; 16] = [0u8; 16];
    let mut v: [u8; 16] = *y;
    for i in 0..16 {
        for j in 0..8 {
            let bit = (x[i] >> (7 - j)) & 1;
            if bit == 1 {
                for k in 0..16 { z[k] ^= v[k]; }
            }
            let lsb = v[15] & 1;
            let mut carry: u8 = 0;
            for k in 0..16 {
                let cur = v[k];
                v[k] = (carry << 7) | (cur >> 1);
                carry = cur & 1;
            }
            if lsb == 1 {
                v[0] ^= 0xe1;
            }
        }
    }
    z
}

#[verifier::external_body]
pub fn gctr_inc32(counter: &mut [u8; 16])
    ensures final(counter)@ == gctr_inc32_spec(old(counter)@),
{
    let mut i: usize = 16;
    let end = 12;
    while i > end {
        i -= 1;
        counter[i] = counter[i].wrapping_add(1);
        if counter[i] != 0 { break; }
    }
}

// ── Verified GHASH chain ──────────────────────────────────────

/// ghash_iterate: Horner chain over 16-byte-aligned `data`.
/// Verified against `ghash_at_spec`.
pub fn ghash_iterate(h: &[u8; 16], data: &[u8]) -> (y: [u8; 16])
    requires
        data@.len() % 16 == 0,
        data@.len() < 0x4000_0000u64,
    ensures y@ == ghash_at_spec(h@, data@, (data@.len() / 16) as int),
{
    let mut y: [u8; 16] = [0u8; 16];
    proof {
        assert(y@ =~= ghash_zero_spec());
    }
    let n = data.len() / 16;
    let mut i: usize = 0;
    let mut off: usize = 0;
    while i < n
        invariant
            i <= n,
            n == data@.len() / 16,
            n * 16 == data@.len(),
            data@.len() % 16 == 0,
            data@.len() < 0x4000_0000u64,
            off == i * 16,
            off <= data@.len(),
            y@ == ghash_at_spec(h@, data@, i as int),
        decreases n - i,
    {
        let mut block: [u8; 16] = [0u8; 16];
        let mut k: usize = 0;
        while k < 16
            invariant
                k <= 16,
                off + 16 <= data@.len(),
                off == i * 16,
                forall|m: int| 0 <= m < k as int ==> block@[m] == data@[off + m],
            decreases 16 - k,
        {
            block[k] = data[off + k];
            k = k + 1;
        }
        proof {
            assert(block@ =~= take_block_spec(data@, (i as int) * 16));
        }
        let mut xored: [u8; 16] = [0u8; 16];
        let mut m: usize = 0;
        while m < 16
            invariant
                m <= 16,
                forall|j: int| 0 <= j < m as int ==> xored@[j] == y@[j] ^ block@[j],
            decreases 16 - m,
        {
            xored[m] = y[m] ^ block[m];
            m = m + 1;
        }
        proof {
            assert(xored@ =~= ghash_xor_spec(y@, block@));
        }
        y = ghash_mul(&xored, h);
        i = i + 1;
        off = off + 16;
    }
    y
}

// ── Verified GCTR chain ───────────────────────────────────────

/// gctr_encrypt: block-to-stream encrypt for GCM (counter starts
/// at J0+1, increments 32-bit). Verified against
/// `gctr_ciphertext_byte_at_spec`.
pub fn gctr_encrypt(
    key: &[u8; 16], j0: &[u8; 16], plaintext: &[u8],
) -> (out: Vec<u8>)
    requires plaintext@.len() < 0x4000_0000u64,
    ensures
        out@.len() == plaintext@.len(),
        forall|k: int| 0 <= k < out@.len()
            ==> out@[k] == gctr_ciphertext_byte_at_spec(key@, j0@, plaintext@, k),
{
    let n = plaintext.len();
    let mut out: Vec<u8> = Vec::with_capacity(n);
    let mut counter: [u8; 16] = *j0;
    gctr_inc32(&mut counter);  // start at J0 + 1
    let mut b: usize = 0;
    let mut off: usize = 0;
    while off + AES128_BLOCK_BYTES <= n
        invariant
            off <= n,
            off == b * AES128_BLOCK_BYTES,
            n == plaintext@.len(),
            n < 0x4000_0000u64,
            counter@ == gctr_counter_at_spec(j0@, b as int),
            out@.len() == off as int,
            forall|k: int| 0 <= k < out@.len()
                ==> out@[k] == gctr_ciphertext_byte_at_spec(key@, j0@, plaintext@, k),
        decreases n - off,
    {
        let ks = aes128_encrypt_block(key, &counter);
        proof {
            assert(ks@ == gctr_keystream_block_at_spec(key@, j0@, b as int));
        }
        let mut k: usize = 0;
        while k < AES128_BLOCK_BYTES
            invariant
                k <= AES128_BLOCK_BYTES,
                off == b * AES128_BLOCK_BYTES,
                off + AES128_BLOCK_BYTES <= n,
                n == plaintext@.len(),
                ks@ == gctr_keystream_block_at_spec(key@, j0@, b as int),
                out@.len() == (off + k) as int,
                forall|m: int| 0 <= m < (off + k) as int
                    ==> out@[m] == gctr_ciphertext_byte_at_spec(key@, j0@, plaintext@, m),
            decreases AES128_BLOCK_BYTES - k,
        {
            let kbyte = ks[k];
            let abs_idx = off + k;
            assert(abs_idx < n);
            proof {
                assert((abs_idx as int) / 16 == b as int);
                assert((abs_idx as int) % 16 == k as int);
            }
            out.push(plaintext[abs_idx] ^ kbyte);
            k = k + 1;
        }
        gctr_inc32(&mut counter);
        off = off + AES128_BLOCK_BYTES;
        b = b + 1;
    }
    // Partial last block.
    if off < n {
        let ks = aes128_encrypt_block(key, &counter);
        proof {
            assert(ks@ == gctr_keystream_block_at_spec(key@, j0@, b as int));
        }
        let remaining = n - off;
        let mut k: usize = 0;
        while k < remaining
            invariant
                k <= remaining,
                remaining == n - off,
                off == b * AES128_BLOCK_BYTES,
                off + remaining == n,
                remaining < AES128_BLOCK_BYTES,
                n == plaintext@.len(),
                ks@ == gctr_keystream_block_at_spec(key@, j0@, b as int),
                out@.len() == (off + k) as int,
                forall|m: int| 0 <= m < (off + k) as int
                    ==> out@[m] == gctr_ciphertext_byte_at_spec(key@, j0@, plaintext@, m),
            decreases remaining - k,
        {
            let kbyte = ks[k];
            let abs_idx = off + k;
            assert(abs_idx < n);
            proof {
                assert((abs_idx as int) / 16 == b as int);
                assert((abs_idx as int) % 16 == k as int);
            }
            out.push(plaintext[abs_idx] ^ kbyte);
            k = k + 1;
        }
    }
    out
}

// ── Top-level AES-128-GCM (external_body composition) ──────────────

#[verifier::external_body]
pub fn aes128_gcm_encrypt(
    key: &[u8; 16], iv: &[u8; 12], aad: &[u8], plaintext: &[u8],
) -> (out: (Vec<u8>, [u8; 16]))
    requires
        plaintext@.len() < 0x4000_0000u64,
        aad@.len() < 0x4000_0000u64,
{
    let zero_block: [u8; 16] = [0u8; 16];
    let h = aes128_encrypt_block(key, &zero_block);
    let mut j0: [u8; 16] = [0u8; 16];
    for i in 0..12 { j0[i] = iv[i]; }
    j0[15] = 1;
    let ciphertext = gctr_encrypt(key, &j0, plaintext);
    let mut gh_input: Vec<u8> = Vec::new();
    for b in aad { gh_input.push(*b); }
    while gh_input.len() % 16 != 0 { gh_input.push(0); }
    for b in &ciphertext { gh_input.push(*b); }
    while gh_input.len() % 16 != 0 { gh_input.push(0); }
    let aad_bits = (aad.len() as u64).wrapping_mul(8);
    let ct_bits  = (ciphertext.len() as u64).wrapping_mul(8);
    let aad_be = aad_bits.to_be_bytes();
    let ct_be  = ct_bits.to_be_bytes();
    for i in 0..8 { gh_input.push(aad_be[i]); }
    for i in 0..8 { gh_input.push(ct_be[i]); }
    let s = ghash_iterate(&h, &gh_input);
    let e_j0 = aes128_encrypt_block(key, &j0);
    let mut tag: [u8; 16] = [0u8; 16];
    for k in 0..16 { tag[k] = s[k] ^ e_j0[k]; }
    (ciphertext, tag)
}

}
