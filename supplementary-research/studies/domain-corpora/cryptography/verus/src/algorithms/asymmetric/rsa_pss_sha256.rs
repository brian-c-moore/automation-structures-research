// RSA-PSS-SHA-256 (PKCS#1 v2.2, RFC 8017).
//
// RSA-PSS-SHA-256 instantiates scalar-multiplication-over-an-
// algebraic-group with modular exponentiation over a 2048-bit RSA
// modulus. The Verus annotations encode the verify operation; the
// concrete bignum / modexp / EMSA-PSS-VERIFY content is in external-
// body code with uninterp spec linkage.
//
// Uninterp top-level spec; external-body implementation (32 × u64 limb
// bignum, naive schoolbook multiplication, shift-subtract modular
// reduction, MGF1 over SHA-256); RSA-PSS KAT vectors validate
// extrinsically.
//
// Verification boundary: written contracts plus named external-body assumptions.

use crate::algorithms::hashes::sha256::sha256;
use vstd::prelude::*;

verus! {

pub const RSA_PSS_MOD_BYTES: usize = 256;  // 2048 bits / 8
pub const SHA256_HASH_BYTES:  usize = 32;
pub const RSA_PSS_LIMBS:      usize = 32;  // 256 bytes / 8 bytes per u64

/// rsa_pss_sha256_verify_spec: deterministic verify function. Uninterp
/// abstraction; the modular-exponentiation chain shape is the
/// structural target. Validated extrinsically by RFC 8017 / NIST
/// CAVP / Wycheproof test vectors. `e` is the RSA public exponent
/// passed through unchanged so the spec accurately describes verify
/// behavior for any e (not just 65537).
pub uninterp spec fn rsa_pss_sha256_verify_spec(
    n: Seq<u8>,
    e: u32,
    message: Seq<u8>,
    signature: Seq<u8>,
) -> bool;

// ── 2048-bit bignum (32 × u64 limbs, little-endian) ────────────────

#[verifier::external_body]
fn bn_from_be_bytes(b: &[u8; 256]) -> [u64; 32] {
    let mut out: [u64; 32] = [0u64; 32];
    for i in 0..32 {
        let off = (32 - 1 - i) * 8;
        out[i] = ((b[off] as u64) << 56)
               | ((b[off + 1] as u64) << 48)
               | ((b[off + 2] as u64) << 40)
               | ((b[off + 3] as u64) << 32)
               | ((b[off + 4] as u64) << 24)
               | ((b[off + 5] as u64) << 16)
               | ((b[off + 6] as u64) << 8)
               | (b[off + 7] as u64);
    }
    out
}

#[verifier::external_body]
fn bn_to_be_bytes(bn: &[u64; 32]) -> [u8; 256] {
    let mut out: [u8; 256] = [0u8; 256];
    for i in 0..32 {
        let off = (32 - 1 - i) * 8;
        let v = bn[i];
        out[off]     = (v >> 56) as u8;
        out[off + 1] = (v >> 48) as u8;
        out[off + 2] = (v >> 40) as u8;
        out[off + 3] = (v >> 32) as u8;
        out[off + 4] = (v >> 24) as u8;
        out[off + 5] = (v >> 16) as u8;
        out[off + 6] = (v >> 8)  as u8;
        out[off + 7] = v as u8;
    }
    out
}

// Compare two 64-limb numbers. Returns -1, 0, 1.
#[verifier::external_body]
fn bn64_cmp(a: &[u64; 64], b: &[u64; 64]) -> i32 {
    let mut i: usize = 64;
    while i > 0 {
        i -= 1;
        if a[i] > b[i] { return 1; }
        if a[i] < b[i] { return -1; }
    }
    0
}

// Subtract b from a (both 64 limbs). Assumes a >= b.
#[verifier::external_body]
fn bn64_sub(a: &mut [u64; 64], b: &[u64; 64]) {
    let mut borrow: u64 = 0;
    for i in 0..64 {
        let (r1, b1) = a[i].overflowing_sub(b[i]);
        let (r2, b2) = r1.overflowing_sub(borrow);
        a[i] = r2;
        borrow = (b1 as u64) | (b2 as u64);
    }
}

// Shift a 32-limb number left by `bits` bits, producing a 64-limb result.
#[verifier::external_body]
fn bn32_shl_to_64(a: &[u64; 32], bits: usize) -> [u64; 64] {
    let mut out: [u64; 64] = [0u64; 64];
    let limb_shift = bits / 64;
    let bit_shift = bits % 64;
    if bit_shift == 0 {
        for i in 0..32 {
            if i + limb_shift < 64 {
                out[i + limb_shift] = a[i];
            }
        }
    } else {
        for i in 0..32 {
            let lo = a[i] << bit_shift;
            let hi = a[i] >> (64 - bit_shift);
            if i + limb_shift < 64 {
                out[i + limb_shift] |= lo;
            }
            if i + limb_shift + 1 < 64 {
                out[i + limb_shift + 1] |= hi;
            }
        }
    }
    out
}

// Schoolbook multiply two 32-limb numbers, producing 64-limb result.
#[verifier::external_body]
fn bn_mul(a: &[u64; 32], b: &[u64; 32]) -> [u64; 64] {
    let mut out: [u64; 64] = [0u64; 64];
    for i in 0..32 {
        let mut carry: u128 = 0;
        for j in 0..32 {
            let prod = (a[i] as u128) * (b[j] as u128)
                     + (out[i + j] as u128) + carry;
            out[i + j] = prod as u64;
            carry = prod >> 64;
        }
        out[i + 32] = carry as u64;
    }
    out
}

// Reduce a 64-limb number mod a 32-limb n. Naive shift-subtract.
#[verifier::external_body]
fn bn_mod(a_in: &[u64; 64], n: &[u64; 32]) -> [u64; 32] {
    let mut a: [u64; 64] = *a_in;
    // For each shift from 2048 bits down to 0, conditionally subtract.
    let mut shift: i32 = 2048;
    while shift >= 0 {
        let shifted_n = bn32_shl_to_64(n, shift as usize);
        if bn64_cmp(&a, &shifted_n) >= 0 {
            bn64_sub(&mut a, &shifted_n);
        }
        shift -= 1;
    }
    let mut out: [u64; 32] = [0u64; 32];
    for i in 0..32 { out[i] = a[i]; }
    out
}

/// bn_modmul_spec: a * b mod n as an abstract field element.
pub uninterp spec fn bn_modmul_spec(a: Seq<u64>, b: Seq<u64>, n: Seq<u64>) -> Seq<u64>;

#[verifier::external_body]
fn bn_modmul(a: &[u64; 32], b: &[u64; 32], n: &[u64; 32]) -> (out: [u64; 32])
    ensures out@ == bn_modmul_spec(a@, b@, n@),
{
    let prod = bn_mul(a, b);
    bn_mod(&prod, n)
}

// ── modexp chain spec (square-and-multiply) ───────────────────

/// bn_one_spec: the field element 1 (representation of 1 in 32 limbs).
pub uninterp spec fn bn_one_spec() -> Seq<u64>;

/// modexp_iter_spec(result, base_acc, exp_remaining, n): the state of
/// the square-and-multiply loop after processing the high bits of the
/// exponent. The exec loop iterates from the LSB up; this spec
/// captures the recurrence.
pub open spec fn modexp_step_spec(
    result: Seq<u64>, base_acc: Seq<u64>, exp_bit: u64, n: Seq<u64>,
) -> Seq<u64> {
    if exp_bit == 1 {
        bn_modmul_spec(result, base_acc, n)
    } else {
        result
    }
}

/// modexp_iter_spec(result_init, base_init, exp, n, k): the
/// accumulator after k square-and-multiply iterations.
pub open spec fn modexp_iter_spec(
    result_init: Seq<u64>, base_init: Seq<u64>, exp: u32, n: Seq<u64>, k: int,
) -> Seq<u64>
    decreases k,
{
    if k <= 0 {
        result_init
    } else {
        let prev_state = modexp_iter_state_spec(result_init, base_init, exp, n, k - 1);
        let cur_bit = exp_bit_at_spec(exp, k - 1);
        modexp_step_spec(prev_state.0, prev_state.1, cur_bit, n)
    }
}

/// modexp_iter_state_spec: the (result, base_acc) pair after k
/// iterations. Recursive over k.
pub open spec fn modexp_iter_state_spec(
    result_init: Seq<u64>, base_init: Seq<u64>, exp: u32, n: Seq<u64>, k: int,
) -> (Seq<u64>, Seq<u64>)
    decreases k,
{
    if k <= 0 {
        (result_init, base_init)
    } else {
        let prev = modexp_iter_state_spec(result_init, base_init, exp, n, k - 1);
        let bit = exp_bit_at_spec(exp, k - 1);
        let new_result = modexp_step_spec(prev.0, prev.1, bit, n);
        let new_base = bn_modmul_spec(prev.1, prev.1, n);
        (new_result, new_base)
    }
}

/// exp_bit_at_spec(exp, k): the k-th bit of exp (LSB-first). Uninterp;
/// the concrete bit extraction is in external-body `extract_bit`.
pub uninterp spec fn exp_bit_at_spec(exp: u32, k: int) -> u64;

#[verifier::external_body]
fn extract_bit(exp: u32, k: usize) -> (out: u64)
    requires k < 32,
    ensures out == exp_bit_at_spec(exp, k as int),
{
    ((exp >> k as u32) & 1) as u64
}

// ── Verified modexp chain ─────────────────────────────────────

/// bn_modexp_u32: result = base^exp mod n via square-and-multiply.
/// Verified against `modexp_iter_state_spec` for 32 iterations (one
/// per exponent bit).
pub fn bn_modexp_u32(base: &[u64; 32], exp: u32, n: &[u64; 32]) -> (out: [u64; 32])
    ensures out@ == modexp_iter_state_spec(bn_one_spec(), base@, exp, n@, 32).0,
{
    let one_arr = bn_one_arr();
    let mut result: [u64; 32] = one_arr;
    let mut base_acc: [u64; 32] = *base;
    let ghost result_init = result@;
    let ghost base_init = base_acc@;
    let mut k: usize = 0;
    while k < 32
        invariant
            k <= 32,
            result_init == bn_one_spec(),
            base_init == base@,
            result@ == modexp_iter_state_spec(result_init, base_init, exp, n@, k as int).0,
            base_acc@ == modexp_iter_state_spec(result_init, base_init, exp, n@, k as int).1,
        decreases 32 - k,
    {
        let bit = extract_bit(exp, k);
        if bit == 1 {
            result = bn_modmul(&result, &base_acc, n);
        }
        base_acc = bn_modmul(&base_acc, &base_acc, n);
        k = k + 1;
    }
    result
}

/// bn_one_arr: the 32-limb representation of 1. External-body; links
/// to `bn_one_spec`.
#[verifier::external_body]
fn bn_one_arr() -> (out: [u64; 32])
    ensures out@ == bn_one_spec(),
{
    let mut o = [0u64; 32];
    o[0] = 1;
    o
}

// ── MGF1 over SHA-256 ───────────────────────────────────────────────

#[verifier::external_body]
fn mgf1_sha256(seed: &[u8], length: usize) -> Vec<u8> {
    let mut out: Vec<u8> = Vec::with_capacity(length);
    let block_count = (length + SHA256_HASH_BYTES - 1) / SHA256_HASH_BYTES;
    for counter in 0..block_count {
        let mut input: Vec<u8> = Vec::with_capacity(seed.len() + 4);
        for b in seed { input.push(*b); }
        let cb = (counter as u32).to_be_bytes();
        input.push(cb[0]); input.push(cb[1]); input.push(cb[2]); input.push(cb[3]);
        let h = sha256(&input);
        let take = if counter == block_count - 1 {
            length - counter * SHA256_HASH_BYTES
        } else {
            SHA256_HASH_BYTES
        };
        for k in 0..take { out.push(h[k]); }
    }
    out
}

// ── EMSA-PSS-VERIFY (RFC 8017 §9.1.2) ────────────────────────────────

#[verifier::external_body]
fn emsa_pss_verify(m: &[u8], em: &[u8; 256], em_bits: u32, s_len: usize) -> bool {
    let h_len = SHA256_HASH_BYTES;
    let em_len = 256usize;

    if em_len < h_len + s_len + 2 { return false; }
    if em[em_len - 1] != 0xbc { return false; }

    let masked_db_len = em_len - h_len - 1;
    let h: [u8; 32] = {
        let mut t = [0u8; 32];
        for i in 0..32 { t[i] = em[masked_db_len + i]; }
        t
    };

    // Verify leftmost bits of em[0] are zero per em_bits constraint.
    let leftmost_unused = (8 * em_len as u32) - em_bits;
    if leftmost_unused > 0 {
        let mask = 0xffu8 << (8 - leftmost_unused);
        if em[0] & mask != 0 { return false; }
    }

    // db_mask = MGF1(H, masked_db_len)
    let db_mask = mgf1_sha256(&h, masked_db_len);
    // db = masked_db XOR db_mask
    let mut db: Vec<u8> = Vec::with_capacity(masked_db_len);
    for i in 0..masked_db_len {
        db.push(em[i] ^ db_mask[i]);
    }
    // Clear leftmost (leftmost_unused) bits of db[0].
    if leftmost_unused > 0 {
        let mask = 0xffu8 >> leftmost_unused;
        db[0] &= mask;
    }

    // db must be: (em_len - s_len - h_len - 2) zeros, then 0x01, then salt (s_len bytes).
    let ps_len = em_len - s_len - h_len - 2;
    for i in 0..ps_len {
        if db[i] != 0 { return false; }
    }
    if db[ps_len] != 0x01 { return false; }

    // salt = db[ps_len + 1 ..]
    let mut salt: Vec<u8> = Vec::with_capacity(s_len);
    for i in 0..s_len {
        salt.push(db[ps_len + 1 + i]);
    }

    // M' = (8 zero bytes) || mHash || salt
    let m_hash = sha256(m);
    let mut m_prime: Vec<u8> = Vec::with_capacity(8 + 32 + s_len);
    for _ in 0..8 { m_prime.push(0); }
    for k in 0..32 { m_prime.push(m_hash[k]); }
    for b in &salt { m_prime.push(*b); }

    let h_prime = sha256(&m_prime);
    for i in 0..32 {
        if h[i] != h_prime[i] { return false; }
    }
    true
}

// ── Top-level RSA-PSS-SHA-256 verify ────────────────────────────────

/// rsa_pss_sha256_verify: full RSA-PSS-SHA-256 verification. Per RFC
/// 8017 §8.1.2:
///   1. Length check on signature.
///   2. OS2IP(sig) -> integer s.
///   3. RSAVP1: m = s^e mod n.
///   4. I2OSP(m) -> em (256 bytes).
///   5. EMSA-PSS-VERIFY(M, em, em_bits = 2047, s_len).
///
/// The signature is the 256-byte representation of s, big-endian.
/// The public key (n, e) is given as big-endian byte sequences.
/// s_len is the salt length used at signing time; this implementation
/// assumes the typical sLen = hLen = 32 unless otherwise specified.
#[verifier::external_body]
pub fn rsa_pss_sha256_verify(
    n: &[u8; 256],
    e: u32,
    message: &[u8],
    signature: &[u8; 256],
    s_len: usize,
) -> (b: bool)
    ensures b == rsa_pss_sha256_verify_spec(n@, e, message@, signature@),
{
    let n_bn = bn_from_be_bytes(n);
    let s_bn = bn_from_be_bytes(signature);

    // Check s < n.
    let mut s_lt_n = false;
    let mut i: usize = 32;
    while i > 0 {
        i -= 1;
        if s_bn[i] < n_bn[i] { s_lt_n = true; break; }
        if s_bn[i] > n_bn[i] { break; }
    }
    if !s_lt_n {
        // s == n or s > n (modulus must be ahead).
        // For exact equality, also reject (signature representative out of range).
        let mut equal = true;
        for k in 0..32 { if s_bn[k] != n_bn[k] { equal = false; break; } }
        if equal { return false; }
        if i == 31 && s_bn[31] > n_bn[31] { return false; }
    }

    let m_bn = bn_modexp_u32(&s_bn, e, &n_bn);
    let em = bn_to_be_bytes(&m_bn);

    // em_bits = 2048 - 1 = 2047 (modBits - 1).
    emsa_pss_verify(message, &em, 2047u32, s_len)
}

}
