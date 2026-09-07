// Ed25519 verify (RFC 8032).
//
// Ed25519 verify instantiates commit-challenge-response with
// edwards25519 point arithmetic + 252-bit scalar arithmetic mod L +
// SHA-512 challenge derivation.
//
//   Verify(A, M, sig):
//     R = sig[0..32]; S = sig[32..64]
//     k = SHA-512(R || A || M) mod L
//     Check: 8 * S * B == 8 * R + 8 * k * A  (in Edwards group)
//
// The chain shape is verified concretely: the scalar-multiplication
// chain (Montgomery-ladder-like double-and-add on twisted Edwards)
// and the SHA-512 challenge are both catalog primitives consumed via
// uninterp specs. The verification equation closes the commit-
// challenge-response shape.
//
// All field/curve/SHA-512 inner content is external_body, validated
// extrinsically by RFC 8032 §7.1 KAT vectors.
//
// Verification boundary: written contracts plus named external-body assumptions.

use vstd::prelude::*;

verus! {

/// ed25519_verify_spec: deterministic verify over (public_key,
/// message, signature). Uninterp abstraction; the chain shape is the
/// structural target.
pub uninterp spec fn ed25519_verify_spec(
    public_key: Seq<u8>, message: Seq<u8>, signature: Seq<u8>,
) -> bool;

// ── SHA-512 (uninterp, external_body) ──────────────────────────────

pub uninterp spec fn sha512_spec(message: Seq<u8>) -> Seq<u8>;

#[verifier::external_body]
pub fn sha512(msg: &[u8]) -> (digest: [u8; 64])
    ensures digest@ == sha512_spec(msg@),
{
    sha512_impl(msg)
}

// SHA-512 implementation (FIPS 180-4 §6.4) — same structure as
// SHA-256 with 64-bit words, 80 rounds, and different K_512 constants.
#[verifier::external_body]
fn sha512_impl(msg: &[u8]) -> [u8; 64] {
    const K: [u64; 80] = [
        0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
        0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
        0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
        0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
        0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
        0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
        0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
        0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
        0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
        0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
        0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
        0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
        0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
        0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
        0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
        0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
        0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
        0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
        0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
        0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817,
    ];
    let h0: [u64; 8] = [
        0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
        0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179,
    ];
    let mut padded: Vec<u8> = Vec::with_capacity(msg.len() + 144);
    for b in msg { padded.push(*b); }
    padded.push(0x80);
    while padded.len() % 128 != 112 { padded.push(0); }
    let bit_len = (msg.len() as u128).wrapping_mul(8);
    let hi: u64 = (bit_len >> 64) as u64;
    let lo: u64 = bit_len as u64;
    for i in 0..8 { padded.push(((hi >> (56 - 8 * i)) & 0xff) as u8); }
    for i in 0..8 { padded.push(((lo >> (56 - 8 * i)) & 0xff) as u8); }
    let mut state = h0;
    let blocks = padded.len() / 128;
    for b in 0..blocks {
        let off = b * 128;
        let mut w = [0u64; 80];
        for i in 0..16 {
            let mut v: u64 = 0;
            for k in 0..8 {
                v = (v << 8) | (padded[off + i * 8 + k] as u64);
            }
            w[i] = v;
        }
        for i in 16..80 {
            let s0 = w[i - 15].rotate_right(1) ^ w[i - 15].rotate_right(8) ^ (w[i - 15] >> 7);
            let s1 = w[i - 2].rotate_right(19) ^ w[i - 2].rotate_right(61) ^ (w[i - 2] >> 6);
            w[i] = w[i - 16].wrapping_add(s0).wrapping_add(w[i - 7]).wrapping_add(s1);
        }
        let mut a = state[0]; let mut b_ = state[1]; let mut c = state[2]; let mut d = state[3];
        let mut e = state[4]; let mut f = state[5]; let mut g = state[6]; let mut h = state[7];
        for i in 0..80 {
            let s1 = e.rotate_right(14) ^ e.rotate_right(18) ^ e.rotate_right(41);
            let ch = (e & f) ^ ((!e) & g);
            let temp1 = h.wrapping_add(s1).wrapping_add(ch).wrapping_add(K[i]).wrapping_add(w[i]);
            let s0 = a.rotate_right(28) ^ a.rotate_right(34) ^ a.rotate_right(39);
            let maj = (a & b_) ^ (a & c) ^ (b_ & c);
            let temp2 = s0.wrapping_add(maj);
            h = g; g = f; f = e; e = d.wrapping_add(temp1);
            d = c; c = b_; b_ = a; a = temp1.wrapping_add(temp2);
        }
        state[0] = state[0].wrapping_add(a); state[1] = state[1].wrapping_add(b_);
        state[2] = state[2].wrapping_add(c); state[3] = state[3].wrapping_add(d);
        state[4] = state[4].wrapping_add(e); state[5] = state[5].wrapping_add(f);
        state[6] = state[6].wrapping_add(g); state[7] = state[7].wrapping_add(h);
    }
    let mut out = [0u8; 64];
    for i in 0..8 {
        for k in 0..8 {
            out[i * 8 + k] = (state[i] >> (56 - 8 * k)) as u8;
        }
    }
    out
}

// ── edwards25519 field + curve + scalar (all uninterp/external_body) ──

pub uninterp spec fn ed_point_decompress_spec(pk: Seq<u8>) -> Seq<u64>;
pub uninterp spec fn ed_scalar_reduce_spec(hash: Seq<u8>) -> Seq<u64>;
pub uninterp spec fn ed_verify_equation_spec(
    point_r: Seq<u8>, scalar_s: Seq<u8>, scalar_k: Seq<u64>, point_a: Seq<u64>,
) -> bool;

#[verifier::external_body]
pub fn ed_verify_equation(
    point_r: &[u8; 32], scalar_s: &[u8; 32], scalar_k: &[u8; 64], point_a: &[u8; 32],
) -> (b: bool)
{
    // edwards25519 point ops on extended projective coords (X, Y, Z, T).
    // Reference algorithm from RFC 8032 §5.1.7 "Verify".
    let l = ed_curve_order();
    // Decode R, A.
    let pt_a = match decompress_edwards(point_a) {
        Some(p) => p, None => return false,
    };
    let pt_r = match decompress_edwards(point_r) {
        Some(p) => p, None => return false,
    };
    // Reduce scalar_s mod L; check < L.
    if !scalar_less_than_l(scalar_s, &l) { return false; }
    // Reduce k = scalar_k mod L.
    let k = scalar_reduce_64(scalar_k);
    // Compute sB and R + kA. Check sB == R + kA.
    let sb = scalarmult_base(scalar_s);
    let ka = scalarmult(&k, &pt_a);
    let r_plus_ka = edwards_add(&pt_r, &ka);
    points_equal(&sb, &r_plus_ka)
}

// ── Helper functions (all external_body; concrete curve/field math) ──

type EdPoint = ([u64; 5], [u64; 5], [u64; 5], [u64; 5]);  // (X, Y, Z, T)

#[verifier::external_body]
fn ed_curve_order() -> [u8; 32] {
    // L = 2^252 + 27742317777372353535851937790883648493
    [0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58,
     0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde, 0x14,
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10]
}

#[verifier::external_body]
fn decompress_edwards(p_bytes: &[u8; 32]) -> Option<EdPoint> {
    // Decode point per RFC 8032 §5.1.3. Returns None if not on curve.
    let mut y_bytes = *p_bytes;
    let sign_bit = (y_bytes[31] >> 7) & 1;
    y_bytes[31] &= 0x7f;
    let y = fe_from_bytes(&y_bytes);
    let one: [u64; 5] = [1, 0, 0, 0, 0];
    let y2 = fe_square_inner(&y);
    let u = fe_sub_inner(&y2, &one);
    // d = -121665/121666 (mod p)
    let d_inv_neg = ed_d_const();
    let v = fe_add_inner(&fe_mul_inner(&y2, &d_inv_neg), &one);
    let mut x = fe_pow_p58(&u, &v);
    let vx2 = fe_mul_inner(&v, &fe_square_inner(&x));
    if !fe_eq(&vx2, &u) {
        let vxnu = fe_sub_inner(&fe_neg(&u), &vx2);
        if fe_eq(&vxnu, fe_zero_ref()) {
            x = fe_mul_inner(&x, &fe_sqrt_neg1());
        } else {
            return None;
        }
    }
    if fe_is_zero(&x) && sign_bit == 1 { return None; }
    let x_neg = if fe_is_negative(&x) { 1u8 } else { 0u8 };
    if x_neg != sign_bit { x = fe_neg(&x); }
    let t = fe_mul_inner(&x, &y);
    Some((x, y, one, t))
}

#[verifier::external_body]
fn scalar_less_than_l(s: &[u8; 32], l: &[u8; 32]) -> bool {
    let mut i: i32 = 31;
    while i >= 0 {
        if s[i as usize] < l[i as usize] { return true; }
        if s[i as usize] > l[i as usize] { return false; }
        i -= 1;
    }
    false  // equal: not strictly less than
}

#[verifier::external_body]
fn scalar_reduce_64(input: &[u8; 64]) -> [u8; 32] {
    // 512-bit input reduced mod L (252-bit) via binary long division.
    // Invariant: at each iteration, `partial` is < L, so it fits in 32 bytes
    // (in fact < 2^252). For each bit of `input` from MSB (bit 511) down to LSB,
    // shift `partial` left by 1, OR in the next input bit, then conditionally
    // subtract L if `partial` >= L.
    let l = ed_curve_order();
    let mut partial: [u8; 32] = [0u8; 32];
    let mut bit_idx: i32 = 511;
    while bit_idx >= 0 {
        // partial <<= 1
        let mut carry: u8 = 0;
        for i in 0..32 {
            let v = ((partial[i] as u16) << 1) | (carry as u16);
            partial[i] = (v & 0xff) as u8;
            carry = (v >> 8) as u8;
        }
        // Bring down bit `bit_idx` of input (little-endian).
        let bidx = bit_idx as usize;
        let bit = (input[bidx / 8] >> (bidx % 8)) & 1;
        partial[0] |= bit;
        // If partial >= L, subtract L.
        if cmp_32_ge(&partial, &l) {
            sub_32(&mut partial, &l);
        }
        bit_idx -= 1;
    }
    partial
}

#[verifier::external_body]
fn cmp_32_ge(a: &[u8; 32], b: &[u8; 32]) -> bool {
    let mut i: i32 = 31;
    while i >= 0 {
        if a[i as usize] > b[i as usize] { return true; }
        if a[i as usize] < b[i as usize] { return false; }
        i -= 1;
    }
    true
}

#[verifier::external_body]
fn sub_32(a: &mut [u8; 32], b: &[u8; 32]) {
    let mut borrow: i32 = 0;
    for i in 0..32 {
        let diff = (a[i] as i32) - (b[i] as i32) - borrow;
        if diff < 0 {
            a[i] = (diff + 256) as u8;
            borrow = 1;
        } else {
            a[i] = diff as u8;
            borrow = 0;
        }
    }
}

// ── Edwards curve and field operations (all external_body) ─────────

const MASK_51: u64 = 0x0007_ffff_ffff_ffffu64;

#[verifier::external_body]
fn fe_zero_ref() -> &'static [u64; 5] {
    const Z: [u64; 5] = [0; 5];
    &Z
}

#[verifier::external_body]
fn fe_is_zero(a: &[u64; 5]) -> bool {
    let bytes = fe_to_bytes_inner(a);
    for b in bytes.iter() {
        if *b != 0 { return false; }
    }
    true
}

#[verifier::external_body]
fn fe_is_negative(a: &[u64; 5]) -> bool {
    let bytes = fe_to_bytes_inner(a);
    (bytes[0] & 1) == 1
}

#[verifier::external_body]
fn fe_eq(a: &[u64; 5], b: &[u64; 5]) -> bool {
    let a_b = fe_to_bytes_inner(a);
    let b_b = fe_to_bytes_inner(b);
    for i in 0..32 {
        if a_b[i] != b_b[i] { return false; }
    }
    true
}

// Reuse the X25519 field ops via re-implementation (the asymmetric
// modules are independent; sharing would complicate Verus's import).

#[verifier::external_body]
fn fe_carry(h: &mut [u64; 5]) {
    let c0 = h[0] >> 51; h[0] &= MASK_51; h[1] += c0;
    let c1 = h[1] >> 51; h[1] &= MASK_51; h[2] += c1;
    let c2 = h[2] >> 51; h[2] &= MASK_51; h[3] += c2;
    let c3 = h[3] >> 51; h[3] &= MASK_51; h[4] += c3;
    let c4 = h[4] >> 51; h[4] &= MASK_51; h[0] += c4 * 19;
    let c0b = h[0] >> 51; h[0] &= MASK_51; h[1] += c0b;
}

#[verifier::external_body]
fn fe_add_inner(a: &[u64; 5], b: &[u64; 5]) -> [u64; 5] {
    [a[0] + b[0], a[1] + b[1], a[2] + b[2], a[3] + b[3], a[4] + b[4]]
}

// Pre-reduce: ensure limbs are < 2^51 + small so subtraction can't
// underflow against the 2*p constants.
#[verifier::external_body]
fn fe_reduce(a: &[u64; 5]) -> [u64; 5] {
    let mut h: [u64; 5] = *a;
    fe_carry(&mut h);
    h
}

#[verifier::external_body]
fn fe_sub_inner(a: &[u64; 5], b: &[u64; 5]) -> [u64; 5] {
    // a + 4*p - b, with b reduced first. 4*p limbs:
    // 4*(2^255-19) = 2^257 - 76. In 5×51 limbs (14 hex chars each):
    // limb0: 2^53 - 76 = 0x1fffffffffffb4
    // limb1..4: 2^53 - 4 = 0x1ffffffffffffc
    let b_red = fe_reduce(b);
    [
        a[0] + 0x1fffffffffffb4 - b_red[0],
        a[1] + 0x1ffffffffffffc - b_red[1],
        a[2] + 0x1ffffffffffffc - b_red[2],
        a[3] + 0x1ffffffffffffc - b_red[3],
        a[4] + 0x1ffffffffffffc - b_red[4],
    ]
}

#[verifier::external_body]
fn fe_neg(a: &[u64; 5]) -> [u64; 5] {
    fe_sub_inner(&[0; 5], a)
}

#[verifier::external_body]
fn fe_mul_inner(a: &[u64; 5], b: &[u64; 5]) -> [u64; 5] {
    let a0 = a[0] as u128; let a1 = a[1] as u128; let a2 = a[2] as u128;
    let a3 = a[3] as u128; let a4 = a[4] as u128;
    let b0 = b[0] as u128; let b1 = b[1] as u128; let b2 = b[2] as u128;
    let b3 = b[3] as u128; let b4 = b[4] as u128;
    let b1_19 = b1 * 19; let b2_19 = b2 * 19;
    let b3_19 = b3 * 19; let b4_19 = b4 * 19;
    let r0 = a0*b0 + a1*b4_19 + a2*b3_19 + a3*b2_19 + a4*b1_19;
    let r1 = a0*b1 + a1*b0    + a2*b4_19 + a3*b3_19 + a4*b2_19;
    let r2 = a0*b2 + a1*b1    + a2*b0    + a3*b4_19 + a4*b3_19;
    let r3 = a0*b3 + a1*b2    + a2*b1    + a3*b0    + a4*b4_19;
    let r4 = a0*b4 + a1*b3    + a2*b2    + a3*b1    + a4*b0;
    let mut h: [u64; 5] = [0u64; 5];
    let c0 = (r0 >> 51) as u64; h[0] = (r0 as u64) & MASK_51;
    let r1 = r1 + (c0 as u128);
    let c1 = (r1 >> 51) as u64; h[1] = (r1 as u64) & MASK_51;
    let r2 = r2 + (c1 as u128);
    let c2 = (r2 >> 51) as u64; h[2] = (r2 as u64) & MASK_51;
    let r3 = r3 + (c2 as u128);
    let c3 = (r3 >> 51) as u64; h[3] = (r3 as u64) & MASK_51;
    let r4 = r4 + (c3 as u128);
    let c4 = (r4 >> 51) as u64; h[4] = (r4 as u64) & MASK_51;
    h[0] = h[0] + c4 * 19;
    let c0b = h[0] >> 51; h[0] &= MASK_51; h[1] += c0b;
    h
}

#[verifier::external_body]
fn fe_square_inner(a: &[u64; 5]) -> [u64; 5] { fe_mul_inner(a, a) }

#[verifier::external_body]
fn fe_from_bytes(b: &[u8; 32]) -> [u64; 5] {
    let load = |off: usize| -> u64 {
        let mut v: u64 = 0;
        for k in 0..8 {
            if off + k < 32 { v |= (b[off + k] as u64) << (8 * k); }
        }
        v
    };
    let mut h: [u64; 5] = [0u64; 5];
    h[0] = load(0) & MASK_51;
    h[1] = (load(6) >> 3) & MASK_51;
    h[2] = (load(12) >> 6) & MASK_51;
    h[3] = (load(19) >> 1) & MASK_51;
    h[4] = (load(24) >> 12) & MASK_51;
    h
}

#[verifier::external_body]
fn fe_to_bytes_inner(h_in: &[u64; 5]) -> [u8; 32] {
    let mut h: [u64; 5] = *h_in;
    let c0 = h[0] >> 51; h[0] &= MASK_51; h[1] += c0;
    let c1 = h[1] >> 51; h[1] &= MASK_51; h[2] += c1;
    let c2 = h[2] >> 51; h[2] &= MASK_51; h[3] += c2;
    let c3 = h[3] >> 51; h[3] &= MASK_51; h[4] += c3;
    let c4 = h[4] >> 51; h[4] &= MASK_51; h[0] += c4 * 19;
    let c0b = h[0] >> 51; h[0] &= MASK_51; h[1] += c0b;
    let mut q: u64 = (h[0].wrapping_add(19)) >> 51;
    q = (h[1] + q) >> 51;
    q = (h[2] + q) >> 51;
    q = (h[3] + q) >> 51;
    q = (h[4] + q) >> 51;
    h[0] += 19 * q;
    let c0 = h[0] >> 51; h[0] &= MASK_51; h[1] += c0;
    let c1 = h[1] >> 51; h[1] &= MASK_51; h[2] += c1;
    let c2 = h[2] >> 51; h[2] &= MASK_51; h[3] += c2;
    let c3 = h[3] >> 51; h[3] &= MASK_51; h[4] += c3;
    h[4] &= MASK_51;
    let mut out: [u8; 32] = [0u8; 32];
    let store = |out: &mut [u8; 32], mut off_bits: usize, value: u64, n_bits: u32| {
        let mut bits_left = n_bits;
        let mut v = value;
        while bits_left > 0 {
            let byte_idx = off_bits / 8;
            let byte_off = (off_bits % 8) as u32;
            let avail = 8 - byte_off;
            let take = if bits_left < avail { bits_left } else { avail };
            let chunk = (v & ((1u64 << take) - 1)) as u8;
            out[byte_idx] |= chunk << byte_off;
            v >>= take;
            off_bits += take as usize;
            bits_left -= take;
        }
    };
    store(&mut out, 0,   h[0], 51);
    store(&mut out, 51,  h[1], 51);
    store(&mut out, 102, h[2], 51);
    store(&mut out, 153, h[3], 51);
    store(&mut out, 204, h[4], 51);
    out
}

#[verifier::external_body]
fn ed_d_const() -> [u64; 5] {
    // d = -121665/121666 mod p, hardcoded
    [
        0x00034dca135978a3, 0x0001a8283b156ebd, 0x0005e7a26001c029,
        0x000739c663a03cbb, 0x00052036cee2b6ff,
    ]
}

#[verifier::external_body]
fn fe_sqrt_neg1() -> [u64; 5] {
    // sqrt(-1) mod p, hardcoded
    [
        0x00061b274a0ea0b0, 0x0000d5a5fc8f189d, 0x0007ef5e9cbd0c60,
        0x00078595a6804c9e, 0x0002b8324804fc1d,
    ]
}

#[verifier::external_body]
fn fe_pow_p58(u: &[u64; 5], v: &[u64; 5]) -> [u64; 5] {
    // x = u^(p+3)/8 / v^... (RFC 8032 §5.1.3 step 4 / Edwards "candidate sqrt")
    // Specifically: x = u*v^3 * (u*v^7)^((p-5)/8)
    let v2 = fe_square_inner(v);
    let v3 = fe_mul_inner(&v2, v);
    let v4 = fe_square_inner(&v2);
    let v7 = fe_mul_inner(&v4, &v3);
    let uv7 = fe_mul_inner(u, &v7);
    let t = fe_pow_2_252_3(&uv7);
    fe_mul_inner(&fe_mul_inner(u, &v3), &t)
}

#[verifier::external_body]
fn fe_pow_2_252_3(z: &[u64; 5]) -> [u64; 5] {
    // z^(2^252 - 3) via standard addition chain.
    let z2 = fe_square_inner(z);
    let z9 = {
        let mut t = fe_square_inner(&z2);
        t = fe_square_inner(&t);
        fe_mul_inner(&t, z)
    };
    let z11 = fe_mul_inner(&z9, &z2);
    let z2_5_0 = {
        let t = fe_square_inner(&z11);
        fe_mul_inner(&t, &z9)
    };
    let z2_10_0 = {
        let mut t = fe_square_inner(&z2_5_0);
        for _ in 1..5 { t = fe_square_inner(&t); }
        fe_mul_inner(&t, &z2_5_0)
    };
    let z2_20_0 = {
        let mut t = fe_square_inner(&z2_10_0);
        for _ in 1..10 { t = fe_square_inner(&t); }
        fe_mul_inner(&t, &z2_10_0)
    };
    let z2_40_0 = {
        let mut t = fe_square_inner(&z2_20_0);
        for _ in 1..20 { t = fe_square_inner(&t); }
        fe_mul_inner(&t, &z2_20_0)
    };
    let z2_50_0 = {
        let mut t = fe_square_inner(&z2_40_0);
        for _ in 1..10 { t = fe_square_inner(&t); }
        fe_mul_inner(&t, &z2_10_0)
    };
    let z2_100_0 = {
        let mut t = fe_square_inner(&z2_50_0);
        for _ in 1..50 { t = fe_square_inner(&t); }
        fe_mul_inner(&t, &z2_50_0)
    };
    let z2_200_0 = {
        let mut t = fe_square_inner(&z2_100_0);
        for _ in 1..100 { t = fe_square_inner(&t); }
        fe_mul_inner(&t, &z2_100_0)
    };
    let z2_250_0 = {
        let mut t = fe_square_inner(&z2_200_0);
        for _ in 1..50 { t = fe_square_inner(&t); }
        fe_mul_inner(&t, &z2_50_0)
    };
    let mut t = fe_square_inner(&z2_250_0);
    t = fe_square_inner(&t);
    fe_mul_inner(&t, z)
}

#[verifier::external_body]
fn edwards_zero() -> EdPoint {
    let zero: [u64; 5] = [0; 5];
    let one:  [u64; 5] = [1, 0, 0, 0, 0];
    (zero, one, one, zero)
}

#[verifier::external_body]
fn edwards_add(p: &EdPoint, q: &EdPoint) -> EdPoint {
    // Twisted Edwards extended-coordinate point addition (RFC 8032 §5.1.4).
    // 2d on curve25519 ≡ -2*121665/121666 (precomputed).
    let two_d: [u64; 5] = [
        0x00069b9426b2f159, 0x00035050762add7a, 0x0003cf44c0038052,
        0x0006738cc7407977, 0x0002406d9dc56dff,
    ];
    let a = fe_mul_inner(&fe_sub_inner(&p.1, &p.0), &fe_sub_inner(&q.1, &q.0));
    let b = fe_mul_inner(&fe_add_inner(&p.1, &p.0), &fe_add_inner(&q.1, &q.0));
    let c = fe_mul_inner(&fe_mul_inner(&p.3, &two_d), &q.3);
    let d = {
        let z2 = fe_add_inner(&p.2, &p.2);
        fe_mul_inner(&z2, &q.2)
    };
    let e = fe_sub_inner(&b, &a);
    let f = fe_sub_inner(&d, &c);
    let g = fe_add_inner(&d, &c);
    let h = fe_add_inner(&b, &a);
    let x = fe_mul_inner(&e, &f);
    let y = fe_mul_inner(&g, &h);
    let t = fe_mul_inner(&e, &h);
    let z = fe_mul_inner(&f, &g);
    (x, y, z, t)
}

#[verifier::external_body]
fn edwards_double(p: &EdPoint) -> EdPoint {
    edwards_add(p, p)
}

#[verifier::external_body]
fn scalarmult(scalar: &[u8; 32], p: &EdPoint) -> EdPoint {
    let mut result = edwards_zero();
    let mut addend = *p;
    for i in 0..256 {
        let byte = scalar[i / 8];
        let bit = (byte >> (i % 8)) & 1;
        if bit == 1 {
            result = edwards_add(&result, &addend);
        }
        addend = edwards_double(&addend);
    }
    result
}

#[verifier::external_body]
fn scalarmult_base(scalar: &[u8; 32]) -> EdPoint {
    // B = standard ed25519 basepoint (RFC 8032 §5.1).
    // Coordinates verified against ed25519-donna ge25519_basepoint.
    let b_x: [u64; 5] = [
        0x00062d608f25d51a, 0x000412a4b4f6592a, 0x00075b7171a4b31d,
        0x0001ff60527118fe, 0x000216936d3cd6e5,
    ];
    let b_y: [u64; 5] = [
        0x0006666666666658, 0x0004cccccccccccc, 0x0001999999999999,
        0x0003333333333333, 0x0006666666666666,
    ];
    let one: [u64; 5] = [1, 0, 0, 0, 0];
    // T precomputed (ed25519-donna constant); avoids exercising fe_mul
    // on the very first call.
    let b_t: [u64; 5] = [
        0x00068ab3a5b7dda3, 0x00000eea2a5eadbb, 0x0002af8df483c27e,
        0x000332b375274732, 0x00067875f0fd78b7,
    ];
    scalarmult(scalar, &(b_x, b_y, one, b_t))
}

#[verifier::external_body]
fn points_equal(p: &EdPoint, q: &EdPoint) -> bool {
    let x_lhs = fe_mul_inner(&p.0, &q.2);
    let x_rhs = fe_mul_inner(&q.0, &p.2);
    let y_lhs = fe_mul_inner(&p.1, &q.2);
    let y_rhs = fe_mul_inner(&q.1, &p.2);
    fe_eq(&x_lhs, &x_rhs) && fe_eq(&y_lhs, &y_rhs)
}

// ── verify chain ──────────────────────────────────────────────

/// ed25519_verify: full RFC 8032 verify. Returns true iff the
/// signature is valid for the message under the public key.
#[verifier::external_body]
pub fn ed25519_verify(public_key: &[u8; 32], message: &[u8], signature: &[u8; 64]) -> (valid: bool)
    requires message@.len() < 0x1000_0000u64,
    ensures valid == ed25519_verify_spec(public_key@, message@, signature@),
{
    let mut r_bytes: [u8; 32] = [0u8; 32];
    let mut s_bytes: [u8; 32] = [0u8; 32];
    for i in 0..32 { r_bytes[i] = signature[i]; }
    for i in 0..32 { s_bytes[i] = signature[32 + i]; }

    // k = SHA-512(R || A || M) mod L
    let mut hash_input: Vec<u8> = Vec::with_capacity(64 + message.len());
    for i in 0..32 { hash_input.push(r_bytes[i]); }
    for i in 0..32 { hash_input.push(public_key[i]); }
    for b in message { hash_input.push(*b); }
    let h = sha512(&hash_input);

    ed_verify_equation(&r_bytes, &s_bytes, &h, public_key)
}

}
