// X25519 (RFC 7748).
//
// X25519 instantiates scalar_multiplication over Curve25519 (the
// Montgomery curve y^2 = x^3 + 486662 x^2 + x over GF(2^255 - 19)).
// The Montgomery ladder traverses the scalar bits high-to-low,
// maintaining (x_2/z_2, x_3/z_3) as projective coordinates of (n*P,
// (n+1)*P). RFC 7748 §5; ties to the constant_time modules.
//
// Uninterp top-level spec; external_body implementation (field
// arithmetic over 2^255 - 19 via 5 × 51-bit unsigned limbs); RFC 7748
// §6.1 test vectors validate.
//
// Verification boundary: written contracts plus named external-body assumptions.

use vstd::prelude::*;

verus! {

/// x25519_spec: the X25519 function as a deterministic map over
/// (scalar, u_coordinate). Uninterp abstraction.
pub uninterp spec fn x25519_spec(scalar: Seq<u8>, u: Seq<u8>) -> Seq<u8>;

// ── ladder-step chain spec ─────────────────────────────────────

/// ladder_step_spec: one Montgomery-ladder step (inner step).
/// Takes the previous (x_2, z_2, x_3, z_3, swap_in), the constant
/// x_1, and the current scalar bit; produces the next state and the
/// next swap flag. Uninterp — the differential-add+double
/// formula is in external-body code with field arithmetic.
pub uninterp spec fn ladder_step_spec(
    x_2: Seq<u64>, z_2: Seq<u64>, x_3: Seq<u64>, z_3: Seq<u64>,
    swap_in: u64, x_1: Seq<u64>, bit: u64,
) -> (Seq<u64>, Seq<u64>, Seq<u64>, Seq<u64>, u64);

/// pow2_int(n) = 2^n as an int.
pub open spec fn pow2_int(n: int) -> int
    decreases n,
{
    if n <= 0 { 1 } else { 2 * pow2_int(n - 1) }
}

/// ladder_bit_spec(scalar, t): extract bit t from the clamped scalar,
/// little-endian byte order, LSB-first within each byte.
pub open spec fn ladder_bit_spec(scalar: Seq<u8>, t: int) -> u64 {
    let byte = scalar[t / 8] as int;
    ((byte / pow2_int(t % 8)) % 2) as u64
}

/// ladder_after_steps_spec: state after n_done ladder iterations,
/// processing scalar bits from index 254 down to 254 - n_done + 1.
/// Recursive; chain shape.
pub open spec fn ladder_after_steps_spec(
    x_2_init: Seq<u64>, z_2_init: Seq<u64>, x_3_init: Seq<u64>, z_3_init: Seq<u64>,
    swap_init: u64, x_1: Seq<u64>, scalar: Seq<u8>, n_done: int,
) -> (Seq<u64>, Seq<u64>, Seq<u64>, Seq<u64>, u64)
    decreases n_done,
{
    if n_done <= 0 {
        (x_2_init, z_2_init, x_3_init, z_3_init, swap_init)
    } else {
        let prev = ladder_after_steps_spec(
            x_2_init, z_2_init, x_3_init, z_3_init, swap_init,
            x_1, scalar, n_done - 1,
        );
        let bit_idx = 255 - n_done;
        let bit = ladder_bit_spec(scalar, bit_idx);
        ladder_step_spec(prev.0, prev.1, prev.2, prev.3, prev.4, x_1, bit)
    }
}

// ── 5 × 51-bit limb field arithmetic over p = 2^255 - 19 ────────────
//
// fe = [u64; 5]; limb i represents the coefficient of 2^(51*i).
// After mul/square the limbs are not fully reduced; helper `fe_carry`
// reduces by propagating carries.

const MASK_51: u64 = 0x0007_ffff_ffff_ffffu64;

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
fn fe_add(a: &[u64; 5], b: &[u64; 5]) -> [u64; 5] {
    let mut out: [u64; 5] = [0u64; 5];
    out[0] = a[0] + b[0];
    out[1] = a[1] + b[1];
    out[2] = a[2] + b[2];
    out[3] = a[3] + b[3];
    out[4] = a[4] + b[4];
    out
}

#[verifier::external_body]
fn fe_sub(a: &[u64; 5], b: &[u64; 5]) -> [u64; 5] {
    // Add 2*p in limbs so subtraction doesn't underflow; 2*p in limbs
    // is [4*MASK_51, 4*MASK_51, 4*MASK_51, 4*MASK_51, 4*MASK_51] minus
    // 2*19 in lowest. Concretely: 0xfffffffffffda, then 0xffffffffffffe four times.
    let mut out: [u64; 5] = [0u64; 5];
    out[0] = a[0] + 0xfffffffffffdau64 - b[0];
    out[1] = a[1] + 0xffffffffffffeu64 - b[1];
    out[2] = a[2] + 0xffffffffffffeu64 - b[2];
    out[3] = a[3] + 0xffffffffffffeu64 - b[3];
    out[4] = a[4] + 0xffffffffffffeu64 - b[4];
    out
}

#[verifier::external_body]
fn fe_mul(a: &[u64; 5], b: &[u64; 5]) -> [u64; 5] {
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

    // Reduce 128-bit accumulators down to 64 bits.
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
fn fe_square(a: &[u64; 5]) -> [u64; 5] {
    fe_mul(a, a)
}

#[verifier::external_body]
fn fe_mul_a24(a: &[u64; 5]) -> [u64; 5] {
    // Multiply by (a+2)/4 = 121665 for Curve25519.
    let r0 = (a[0] as u128) * 121665;
    let r1 = (a[1] as u128) * 121665;
    let r2 = (a[2] as u128) * 121665;
    let r3 = (a[3] as u128) * 121665;
    let r4 = (a[4] as u128) * 121665;
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
fn fe_invert(z: &[u64; 5]) -> [u64; 5] {
    // Fermat's little theorem: z^(p-2) = z^(2^255 - 21).
    // 2^255 - 21 in binary: 0b...1111 (251 ones) 01011 — explicit
    // addition chain (Bernstein's standard) computes it in 254 sq + 11 mul.
    let z2 = fe_square(z);
    let z9 = {
        let t = fe_square(&z2);  // z^4
        let t = fe_square(&t);   // z^8
        fe_mul(&t, z)            // z^9
    };
    let z11 = fe_mul(&z9, &z2);  // z^11
    let z2_5_0 = {
        let t = fe_square(&z11); // z^22
        fe_mul(&t, &z9)          // z^31 = z^(2^5 - 1)
    };
    let z2_10_0 = {
        let mut t = fe_square(&z2_5_0);
        for _ in 1..5 { t = fe_square(&t); }
        fe_mul(&t, &z2_5_0)      // z^(2^10 - 1)
    };
    let z2_20_0 = {
        let mut t = fe_square(&z2_10_0);
        for _ in 1..10 { t = fe_square(&t); }
        fe_mul(&t, &z2_10_0)     // z^(2^20 - 1)
    };
    let z2_40_0 = {
        let mut t = fe_square(&z2_20_0);
        for _ in 1..20 { t = fe_square(&t); }
        fe_mul(&t, &z2_20_0)     // z^(2^40 - 1)
    };
    let z2_50_0 = {
        let mut t = fe_square(&z2_40_0);
        for _ in 1..10 { t = fe_square(&t); }
        fe_mul(&t, &z2_10_0)     // z^(2^50 - 1)
    };
    let z2_100_0 = {
        let mut t = fe_square(&z2_50_0);
        for _ in 1..50 { t = fe_square(&t); }
        fe_mul(&t, &z2_50_0)     // z^(2^100 - 1)
    };
    let z2_200_0 = {
        let mut t = fe_square(&z2_100_0);
        for _ in 1..100 { t = fe_square(&t); }
        fe_mul(&t, &z2_100_0)    // z^(2^200 - 1)
    };
    let z2_250_0 = {
        let mut t = fe_square(&z2_200_0);
        for _ in 1..50 { t = fe_square(&t); }
        fe_mul(&t, &z2_50_0)     // z^(2^250 - 1)
    };
    // Finally z^(2^255 - 21) = (z^(2^250-1))^(2^5) * z^11
    let mut t = fe_square(&z2_250_0);
    for _ in 1..5 { t = fe_square(&t); }
    fe_mul(&t, &z11)
}

#[verifier::external_body]
fn fe_from_bytes(b: &[u8; 32]) -> [u64; 5] {
    let load = |off: usize, bits: u32| -> u64 {
        let mut v: u64 = 0;
        let n_bytes = ((bits + 7) / 8) as usize;
        for k in 0..n_bytes {
            v |= (b[off + k] as u64) << (8 * k);
        }
        v
    };
    let mut h: [u64; 5] = [0u64; 5];
    h[0] = load(0, 64) & MASK_51;
    h[1] = (load(6, 64) >> 3) & MASK_51;
    h[2] = (load(12, 64) >> 6) & MASK_51;
    h[3] = (load(19, 64) >> 1) & MASK_51;
    h[4] = (load(24, 64) >> 12) & MASK_51;
    h
}

#[verifier::external_body]
fn fe_to_bytes(h_in: &[u64; 5]) -> [u8; 32] {
    let mut h: [u64; 5] = *h_in;
    fe_carry(&mut h);
    // Subtract p if h >= p.
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

    // Pack 5 × 51-bit limbs into 32 little-endian bytes.
    let v: [u64; 5] = h;
    let mut out: [u8; 32] = [0u8; 32];
    // The standard packing: bytes are little-endian, limb i contributes
    // bits [51*i .. 51*(i+1)).
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
    store(&mut out, 0,   v[0], 51);
    store(&mut out, 51,  v[1], 51);
    store(&mut out, 102, v[2], 51);
    store(&mut out, 153, v[3], 51);
    store(&mut out, 204, v[4], 51);
    out
}

#[verifier::external_body]
fn fe_cswap(swap: u64, a: &mut [u64; 5], b: &mut [u64; 5]) {
    let mask = swap.wrapping_neg();
    for i in 0..5 {
        let t = mask & (a[i] ^ b[i]);
        a[i] ^= t;
        b[i] ^= t;
    }
}

// ── ladder-step exec wrapper (external_body, linked to spec) ───

#[verifier::external_body]
pub fn ladder_step(
    x_2: &mut [u64; 5], z_2: &mut [u64; 5],
    x_3: &mut [u64; 5], z_3: &mut [u64; 5],
    swap_in: u64, x_1: &[u64; 5], bit: u64,
) -> (swap_out: u64)
    ensures
        ({
            let result = ladder_step_spec(
                old(x_2)@, old(z_2)@, old(x_3)@, old(z_3)@,
                swap_in, x_1@, bit);
            &&& final(x_2)@ == result.0
            &&& final(z_2)@ == result.1
            &&& final(x_3)@ == result.2
            &&& final(z_3)@ == result.3
            &&& swap_out == result.4
        }),
{
    let mut swap = swap_in ^ bit;
    fe_cswap(swap, x_2, x_3);
    fe_cswap(swap, z_2, z_3);
    swap = bit;
    let a = fe_add(x_2, z_2);
    let aa = fe_square(&a);
    let b = fe_sub(x_2, z_2);
    let bb = fe_square(&b);
    let e = fe_sub(&aa, &bb);
    let c = fe_add(x_3, z_3);
    let d = fe_sub(x_3, z_3);
    let da = fe_mul(&d, &a);
    let cb = fe_mul(&c, &b);
    let sum_dacb = fe_add(&da, &cb);
    *x_3 = fe_square(&sum_dacb);
    let diff_dacb = fe_sub(&da, &cb);
    let diff_sq = fe_square(&diff_dacb);
    *z_3 = fe_mul(x_1, &diff_sq);
    *x_2 = fe_mul(&aa, &bb);
    let a24e = fe_mul_a24(&e);
    let aa_plus = fe_add(&aa, &a24e);
    *z_2 = fe_mul(&e, &aa_plus);
    swap
}

// ── External-body scalar bit extract, linked to ladder_bit_spec ─────

#[verifier::external_body]
pub fn ladder_bit(scalar: &[u8; 32], t: usize) -> (bit: u64)
    requires t < 256,
    ensures bit == ladder_bit_spec(scalar@, t as int),
{
    ((scalar[t / 8] >> (t as u32 % 8)) & 1) as u64
}

// ── Verified 255-step ladder chain ─────────────────────────────

/// montgomery_ladder: iterate `ladder_step` 255 times from scalar bit
/// 254 down to bit 0. Verified against `ladder_after_steps_spec`.
pub fn montgomery_ladder(
    x_2: &mut [u64; 5], z_2: &mut [u64; 5],
    x_3: &mut [u64; 5], z_3: &mut [u64; 5],
    x_1: &[u64; 5], scalar: &[u8; 32],
) -> (swap_out: u64)
    ensures
        ({
            let result = ladder_after_steps_spec(
                old(x_2)@, old(z_2)@, old(x_3)@, old(z_3)@,
                0u64, x_1@, scalar@, 255);
            &&& final(x_2)@ == result.0
            &&& final(z_2)@ == result.1
            &&& final(x_3)@ == result.2
            &&& final(z_3)@ == result.3
            &&& swap_out == result.4
        }),
{
    let ghost x2_init = old(x_2)@;
    let ghost z2_init = old(z_2)@;
    let ghost x3_init = old(x_3)@;
    let ghost z3_init = old(z_3)@;
    let mut swap: u64 = 0;
    let mut n_done: usize = 0;
    while n_done < 255
        invariant
            n_done <= 255,
            ({
                let result = ladder_after_steps_spec(
                    x2_init, z2_init, x3_init, z3_init,
                    0u64, x_1@, scalar@, n_done as int);
                &&& x_2@ == result.0
                &&& z_2@ == result.1
                &&& x_3@ == result.2
                &&& z_3@ == result.3
                &&& swap == result.4
            }),
        decreases 255 - n_done,
    {
        let bit_idx: usize = 254 - n_done;
        let bit = ladder_bit(scalar, bit_idx);
        proof {
            assert(bit_idx as int == 255 - ((n_done as int) + 1));
            assert(bit == ladder_bit_spec(scalar@, 255 - ((n_done as int) + 1)));
        }
        swap = ladder_step(x_2, z_2, x_3, z_3, swap, x_1, bit);
        n_done = n_done + 1;
    }
    swap
}

// ── X25519 main function ─────────────────────────────────────────────

#[verifier::external_body]
pub fn x25519(scalar: &[u8; 32], u_coord: &[u8; 32]) -> (out: [u8; 32])
    ensures out@ == x25519_spec(scalar@, u_coord@),
{
    // Clamp scalar per RFC 7748 §5.
    let mut k: [u8; 32] = *scalar;
    k[0] &= 248;
    k[31] &= 127;
    k[31] |= 64;

    // Clear u's top bit (MASK off bit 255).
    let mut u_bytes: [u8; 32] = *u_coord;
    u_bytes[31] &= 127;
    let x_1 = fe_from_bytes(&u_bytes);

    let one: [u64; 5] = [1, 0, 0, 0, 0];
    let zero: [u64; 5] = [0, 0, 0, 0, 0];
    let mut x_2 = one;
    let mut z_2 = zero;
    let mut x_3 = x_1;
    let mut z_3 = one;

    let swap = montgomery_ladder(&mut x_2, &mut z_2, &mut x_3, &mut z_3, &x_1, &k);

    fe_cswap(swap, &mut x_2, &mut x_3);
    fe_cswap(swap, &mut z_2, &mut z_3);

    let z_inv = fe_invert(&z_2);
    let result = fe_mul(&x_2, &z_inv);
    fe_to_bytes(&result)
}

}
