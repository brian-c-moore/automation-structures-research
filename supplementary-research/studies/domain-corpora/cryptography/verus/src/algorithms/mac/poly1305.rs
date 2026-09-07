// Poly1305 (RFC 8439 §2.5).
//
// Poly1305 instantiates polynomial-MAC over GF(2^130 - 5). Each
// 16-byte block becomes a 128-bit integer with the 0x01 bit appended
// (so effectively a 17-byte value bounded by 2^128 + 1); the Horner
// accumulator updates as acc_i = (acc_{i-1} + block_i) * r mod p,
// where r is the clamped 16-byte key fragment. The final tag is
// (acc_n + s) mod 2^128 where s is the second 16-byte key fragment.
//
// The chain shape is verified concretely. The GF(2^130 - 5) arithmetic
// (5 × 26-bit limb representation) is the inner content and stays
// uninterp + external_body; the outer block-iteration
// chain is verified via loop invariant matching the recursive
// `poly1305_horner_spec`.
//
// Verification boundary: written contracts plus named external-body assumptions.

use vstd::prelude::*;

verus! {

pub const POLY1305_BLOCK_BYTES: usize = 16;
pub const POLY1305_KEY_BYTES:   usize = 32;
pub const POLY1305_TAG_BYTES:   usize = 16;

// ── Uninterp inner content: field-element types and operations ──────

/// poly_fe_spec: an abstract Poly1305 field element (mathematically a
/// representative in [0, 2^130 - 5)). Uninterp abstraction; the concrete
/// 5 × 26-bit limb representation is external_body.
pub uninterp spec fn poly_fe_zero_spec() -> Seq<u64>;

/// block_to_fe_spec: convert a 16-byte block (with the implicit
/// 0x01 high bit appended per RFC 8439 §2.5.1) into a field element.
pub uninterp spec fn block_to_fe_spec(block: Seq<u8>, full_len: int) -> Seq<u64>;

/// fe_add_spec / fe_mul_spec: field add/mul mod 2^130-5.
pub uninterp spec fn fe_add_spec(a: Seq<u64>, b: Seq<u64>) -> Seq<u64>;
pub uninterp spec fn fe_mul_spec(a: Seq<u64>, b: Seq<u64>) -> Seq<u64>;

/// r_from_key_spec: extract the clamped multiplier r from key[0..16].
pub uninterp spec fn r_from_key_spec(key: Seq<u8>) -> Seq<u64>;

/// finalize_spec: produce the 16-byte tag from the final accumulator
/// and key[16..32] (s mask).
pub uninterp spec fn finalize_spec(acc: Seq<u64>, key: Seq<u8>) -> Seq<u8>;

// ── Horner chain spec ──────────────────────────────────────────

/// take_block_spec(message, off, len): the 16-byte block (or shorter
/// partial block) starting at offset `off` in `message`.
pub open spec fn take_block_spec(message: Seq<u8>, off: int, len: int) -> Seq<u8> {
    Seq::<u8>::new(len as nat, |i: int| message[off + i])
}

/// block_count_spec: ceil(len / 16) — the number of Horner steps.
pub open spec fn block_count_spec(msg_len: int) -> int {
    (msg_len + 15) / 16
}

/// horner_at_spec(message, r, k): the Horner accumulator after the
/// first k blocks. Recursive over k; mirrors `horner_at`.
pub open spec fn horner_at_spec(message: Seq<u8>, r: Seq<u64>, k: int) -> Seq<u64>
    decreases k,
{
    if k <= 0 {
        poly_fe_zero_spec()
    } else if k > block_count_spec(message.len() as int) {
        poly_fe_zero_spec()
    } else {
        let block_off = (k - 1) * 16;
        let block_end = if block_off + 16 > message.len() as int {
            message.len() as int
        } else {
            block_off + 16
        };
        let this_len = block_end - block_off;
        let block = take_block_spec(message, block_off, this_len);
        let block_fe = block_to_fe_spec(block, this_len);
        fe_mul_spec(fe_add_spec(horner_at_spec(message, r, k - 1), block_fe), r)
    }
}

/// poly1305_spec: the full Poly1305 tag.
pub open spec fn poly1305_spec(key: Seq<u8>, message: Seq<u8>) -> Seq<u8> {
    let r = r_from_key_spec(key);
    let acc = horner_at_spec(message, r, block_count_spec(message.len() as int));
    finalize_spec(acc, key)
}

// ── External-body field operations ──────────────────────────────────

/// FE: opaque 5 × u64 representation (5 × 26-bit limbs). The concrete
/// arithmetic is external_body; spec view is `Seq<u64>` of length 5.

#[verifier::external_body]
fn fe_zero() -> (out: [u64; 5])
    ensures out@ == poly_fe_zero_spec(),
{
    [0u64; 5]
}

#[verifier::external_body]
fn r_from_key(key: &[u8; 32]) -> (out: [u64; 5])
    ensures out@ == r_from_key_spec(key@),
{
    let mut clamped = [0u8; 16];
    for i in 0..16 { clamped[i] = key[i]; }
    clamped[3]  &= 15;  clamped[7]  &= 15;  clamped[11] &= 15;  clamped[15] &= 15;
    clamped[4]  &= 252; clamped[8]  &= 252; clamped[12] &= 252;
    let r0 = (u32::from_le_bytes([clamped[0], clamped[1], clamped[2], clamped[3]])
              & 0x03ff_ffff) as u64;
    let r1 = ((u32::from_le_bytes([clamped[3], clamped[4], clamped[5], clamped[6]])
              >> 2) & 0x03ff_ff03) as u64;
    let r2 = ((u32::from_le_bytes([clamped[6], clamped[7], clamped[8], clamped[9]])
              >> 4) & 0x03ff_c0ff) as u64;
    let r3 = ((u32::from_le_bytes([clamped[9], clamped[10], clamped[11], clamped[12]])
              >> 6) & 0x03f0_3fff) as u64;
    let r4 = ((u32::from_le_bytes([clamped[12], clamped[13], clamped[14], clamped[15]])
              >> 8) & 0x000f_ffff) as u64;
    [r0, r1, r2, r3, r4]
}

#[verifier::external_body]
fn fe_add(a: &[u64; 5], b: &[u64; 5]) -> (out: [u64; 5])
    ensures out@ == fe_add_spec(a@, b@),
{
    [a[0] + b[0], a[1] + b[1], a[2] + b[2], a[3] + b[3], a[4] + b[4]]
}

#[verifier::external_body]
fn fe_mul(a: &[u64; 5], r: &[u64; 5]) -> (out: [u64; 5])
    ensures out@ == fe_mul_spec(a@, r@),
{
    let s1 = r[1] * 5; let s2 = r[2] * 5; let s3 = r[3] * 5; let s4 = r[4] * 5;
    let d0 = a[0]*r[0] + a[1]*s4 + a[2]*s3 + a[3]*s2 + a[4]*s1;
    let mut d1 = a[0]*r[1] + a[1]*r[0] + a[2]*s4 + a[3]*s3 + a[4]*s2;
    let mut d2 = a[0]*r[2] + a[1]*r[1] + a[2]*r[0] + a[3]*s4 + a[4]*s3;
    let mut d3 = a[0]*r[3] + a[1]*r[2] + a[2]*r[1] + a[3]*r[0] + a[4]*s4;
    let mut d4 = a[0]*r[4] + a[1]*r[3] + a[2]*r[2] + a[3]*r[1] + a[4]*r[0];
    let mut h: [u64; 5] = [0u64; 5];
    let mut c = d0 >> 26;       h[0] = d0 & 0x03ff_ffff;
    d1 += c; c = d1 >> 26;      h[1] = d1 & 0x03ff_ffff;
    d2 += c; c = d2 >> 26;      h[2] = d2 & 0x03ff_ffff;
    d3 += c; c = d3 >> 26;      h[3] = d3 & 0x03ff_ffff;
    d4 += c; c = d4 >> 26;      h[4] = d4 & 0x03ff_ffff;
    h[0] += c * 5; c = h[0] >> 26;  h[0] &= 0x03ff_ffff;
    h[1] += c;
    h
}

#[verifier::external_body]
fn block_to_fe(message: &[u8], off: usize, full_len: usize) -> (out: [u64; 5])
    requires off + full_len <= message@.len(),
    ensures out@ == block_to_fe_spec(take_block_spec(message@, off as int, full_len as int), full_len as int),
{
    let mut block: [u8; 17] = [0u8; 17];
    for k in 0..full_len { block[k] = message[off + k]; }
    block[full_len] = 1;
    let t0 = u32::from_le_bytes([block[0], block[1], block[2], block[3]]) as u64;
    let t1 = u32::from_le_bytes([block[4], block[5], block[6], block[7]]) as u64;
    let t2 = u32::from_le_bytes([block[8], block[9], block[10], block[11]]) as u64;
    let t3 = u32::from_le_bytes([block[12], block[13], block[14], block[15]]) as u64;
    let t4 = block[16] as u64;
    [
        t0 & 0x03ff_ffff,
        ((t0 >> 26) | (t1 << 6)) & 0x03ff_ffff,
        ((t1 >> 20) | (t2 << 12)) & 0x03ff_ffff,
        ((t2 >> 14) | (t3 << 18)) & 0x03ff_ffff,
        (t3 >> 8) | (t4 << 24),
    ]
}

#[verifier::external_body]
fn finalize(acc: &[u64; 5], key: &[u8; 32]) -> (tag: [u8; 16])
    ensures tag@ == finalize_spec(acc@, key@),
{
    let mut h: [u64; 5] = *acc;
    let mut c = h[1] >> 26; h[1] &= 0x03ff_ffff;
    h[2] += c; c = h[2] >> 26; h[2] &= 0x03ff_ffff;
    h[3] += c; c = h[3] >> 26; h[3] &= 0x03ff_ffff;
    h[4] += c; c = h[4] >> 26; h[4] &= 0x03ff_ffff;
    h[0] += c * 5; c = h[0] >> 26; h[0] &= 0x03ff_ffff;
    h[1] += c;
    let g0 = h[0] + 5;
    let c1 = g0 >> 26; let g0 = g0 & 0x03ff_ffff;
    let g1 = h[1] + c1; let c2 = g1 >> 26; let g1 = g1 & 0x03ff_ffff;
    let g2 = h[2] + c2; let c3 = g2 >> 26; let g2 = g2 & 0x03ff_ffff;
    let g3 = h[3] + c3; let c4 = g3 >> 26; let g3 = g3 & 0x03ff_ffff;
    let g4 = h[4] + c4; let g4 = g4.wrapping_sub(1u64 << 26);
    let mask = (g4 >> 63).wrapping_sub(1);
    let nmask = !mask;
    h[0] = (h[0] & nmask) | (g0 & mask);
    h[1] = (h[1] & nmask) | (g1 & mask);
    h[2] = (h[2] & nmask) | (g2 & mask);
    h[3] = (h[3] & nmask) | (g3 & mask);
    h[4] = (h[4] & nmask) | (g4 & mask);
    let p0 = (h[0] | (h[1] << 26)) & 0xffff_ffff;
    let p1 = ((h[1] >> 6) | (h[2] << 20)) & 0xffff_ffff;
    let p2 = ((h[2] >> 12) | (h[3] << 14)) & 0xffff_ffff;
    let p3 = ((h[3] >> 18) | (h[4] << 8)) & 0xffff_ffff;
    let s0 = u32::from_le_bytes([key[16], key[17], key[18], key[19]]) as u64;
    let s1 = u32::from_le_bytes([key[20], key[21], key[22], key[23]]) as u64;
    let s2 = u32::from_le_bytes([key[24], key[25], key[26], key[27]]) as u64;
    let s3 = u32::from_le_bytes([key[28], key[29], key[30], key[31]]) as u64;
    let f0 = p0 + s0;
    let f1 = p1 + s1 + (f0 >> 32);
    let f2 = p2 + s2 + (f1 >> 32);
    let f3 = p3 + s3 + (f2 >> 32);
    let mut tag = [0u8; 16];
    let f0b = (f0 as u32).to_le_bytes();
    let f1b = (f1 as u32).to_le_bytes();
    let f2b = (f2 as u32).to_le_bytes();
    let f3b = (f3 as u32).to_le_bytes();
    for i in 0..4 { tag[i] = f0b[i]; }
    for i in 0..4 { tag[4 + i] = f1b[i]; }
    for i in 0..4 { tag[8 + i] = f2b[i]; }
    for i in 0..4 { tag[12 + i] = f3b[i]; }
    tag
}

// ── Verified Horner chain executable ───────────────────────────

/// poly1305_horner: iterate the Horner accumulator over the message's
/// blocks. The loop invariant captures `horner_at_spec`; the post-
/// condition closes for Poly1305.
pub fn poly1305_horner(message: &[u8], r: &[u64; 5]) -> (acc: [u64; 5])
    requires message@.len() < 0x4000_0000u64,
    ensures
        acc@ == horner_at_spec(message@, r@, block_count_spec(message@.len() as int)),
{
    let n = message.len();
    let block_count = (n + 15) / 16;
    let mut acc: [u64; 5] = fe_zero();
    let mut k: usize = 0;
    let ghost target_count = block_count_spec(message@.len() as int);
    while k < block_count
        invariant
            k <= block_count,
            block_count == (n + 15) / 16,
            n == message@.len(),
            target_count == block_count_spec(message@.len() as int),
            block_count == target_count,
            acc@ == horner_at_spec(message@, r@, k as int),
        decreases block_count - k,
    {
        let block_off = k * 16;
        let remaining = n - block_off;
        let this_len = if remaining >= 16 { 16 } else { remaining };
        let block_fe = block_to_fe(message, block_off, this_len);
        let sum = fe_add(&acc, &block_fe);
        acc = fe_mul(&sum, r);
        k = k + 1;
    }
    acc
}

#[verifier::external_body]
pub fn poly1305_mac(key: &[u8; 32], message: &[u8]) -> (tag: [u8; 16])
    requires message@.len() < 0x4000_0000u64,
    ensures tag@ == poly1305_spec(key@, message@),
{
    let r = r_from_key(key);
    let acc = poly1305_horner(message, &r);
    finalize(&acc, key)
}

}
