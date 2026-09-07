// PBKDF2-HMAC-SHA-256 (RFC 2898 §5.2).
//
// PBKDF2-HMAC-SHA-256 instantiates iteration_stretching on top of
// HMAC-SHA-256.
//
//   For each output block i (1..n):
//     U_1 = HMAC(password, salt || i_be32)
//     U_j = HMAC(password, U_{j-1})  for j = 2..iterations
//     T_i = U_1 XOR U_2 XOR ... XOR U_iterations
//   DK = T_1 || T_2 || ... || T_n  truncated to `dk_len`.
//
// The chain shape is verified concretely. HMAC-SHA-256 is consumed as a
// primitive via the uninterp `hmac_primitive_spec`. The iteration
// chain (u_at_spec, t_xor_at_spec) is captured by recursive spec
// functions and verified against the executable via loop invariants.
//
// Verification boundary: written contracts plus named external-body assumptions.

use crate::algorithms::kdf::hkdf_sha256::hmac_primitive_spec;
use crate::algorithms::mac::hmac_sha256::hmac_sha256;
use vstd::prelude::*;

verus! {

pub const PBKDF2_HASH_BYTES: usize = 32;

// ── U-chain spec ───────────────────────────────────────────────

/// pbkdf2_salt_i_spec(salt, i): salt || i (big-endian u32 byte).
pub open spec fn pbkdf2_salt_i_spec(salt: Seq<u8>, i: u32) -> Seq<u8> {
    salt
        .push(((i >> 24) & 0xff) as u8)
        .push(((i >> 16) & 0xff) as u8)
        .push(((i >> 8)  & 0xff) as u8)
        .push((i & 0xff) as u8)
}

/// u_at_spec(password, salt, i, j): U_j for output block i. The 
/// chain — U_1 = HMAC(password, salt || i_be32), U_j = HMAC(password,
/// U_{j-1}) for j >= 2.
pub open spec fn u_at_spec(password: Seq<u8>, salt: Seq<u8>, i: u32, j: int) -> Seq<u8>
    decreases j,
{
    if j <= 0 {
        Seq::<u8>::empty()
    } else if j == 1 {
        hmac_primitive_spec(password, pbkdf2_salt_i_spec(salt, i))
    } else {
        hmac_primitive_spec(password, u_at_spec(password, salt, i, j - 1))
    }
}

/// xor_seq_spec(a, b): elementwise XOR (assuming equal length).
pub open spec fn xor_seq_spec(a: Seq<u8>, b: Seq<u8>) -> Seq<u8> {
    Seq::<u8>::new(a.len(), |k: int| a[k] ^ b[k])
}

/// t_xor_at_spec(password, salt, i, j): the running XOR of U_1..U_j
/// for output block i. Recursive over j.
pub open spec fn t_xor_at_spec(password: Seq<u8>, salt: Seq<u8>, i: u32, j: int) -> Seq<u8>
    decreases j,
{
    if j <= 0 {
        Seq::<u8>::new(32, |_k: int| 0u8)
    } else {
        xor_seq_spec(
            t_xor_at_spec(password, salt, i, j - 1),
            u_at_spec(password, salt, i, j),
        )
    }
}

/// pbkdf2_block_spec(password, salt, iterations, i): T_i, the i-th
/// output block.
pub open spec fn pbkdf2_block_spec(
    password: Seq<u8>,
    salt: Seq<u8>,
    iterations: int,
    i: u32,
) -> Seq<u8> {
    t_xor_at_spec(password, salt, i, iterations)
}

/// pbkdf2_hmac_sha256_spec: the full DK as a concatenation of T_i
/// blocks truncated to dk_len.
pub uninterp spec fn pbkdf2_hmac_sha256_spec(
    password: Seq<u8>,
    salt: Seq<u8>,
    iterations: int,
    dk_len: int,
) -> Seq<u8>;

// ── Bitwise lemmas ──────────────────────────────────────────────────

pub proof fn lemma_xor_zero_u8(x: u8)
    ensures (0u8 ^ x) == x,
{
    assert((0u8 ^ x) == x) by (bit_vector);
}

// ── External-body HMAC wrapper ──────────────────────────────────────

#[verifier::external_body]
fn hmac_with_spec(key: &[u8], message: &[u8]) -> (mac: [u8; 32])
    requires
        message@.len() < 0x2000_0000_0000_0000u64,
        key@.len() < 0x2000_0000u64,
    ensures mac@ == hmac_primitive_spec(key@, message@),
{
    hmac_sha256(key, message)
}

// ── Verified salt-with-counter construction ────────────────────────

pub fn build_salt_i(salt: &[u8], i: u32) -> (out: Vec<u8>)
    requires salt@.len() < 0x1000_0000u64,
    ensures
        out@ == pbkdf2_salt_i_spec(salt@, i),
{
    let mut out: Vec<u8> = Vec::with_capacity(salt.len() + 4);
    let mut k: usize = 0;
    while k < salt.len()
        invariant
            k <= salt@.len(),
            out@.len() == k as int,
            forall|j: int| 0 <= j < k as int ==> out@[j] == salt@[j],
        decreases salt@.len() - k,
    {
        out.push(salt[k]);
        k = k + 1;
    }
    proof { assert(out@ =~= salt@); }
    let b0 = ((i >> 24) & 0xff) as u8;
    let b1 = ((i >> 16) & 0xff) as u8;
    let b2 = ((i >> 8)  & 0xff) as u8;
    let b3 = (i & 0xff) as u8;
    out.push(b0); out.push(b1); out.push(b2); out.push(b3);
    proof {
        assert(out@ =~= pbkdf2_salt_i_spec(salt@, i));
    }
    out
}

// ── Verified inner iteration (U-chain + running XOR) ───────────

/// pbkdf2_inner_chain: compute T_i = XOR_{j=1..iterations} U_j for one
/// output block. Verified against `pbkdf2_block_spec`.
pub fn pbkdf2_inner_chain(
    password: &[u8],
    salt: &[u8],
    iterations: u32,
    i: u32,
) -> (t_i: [u8; 32])
    requires
        password@.len() < 0x2000_0000u64,
        salt@.len() < 0x1000_0000u64,
        iterations >= 1,
    ensures
        t_i@ == pbkdf2_block_spec(password@, salt@, iterations as int, i),
{
    let salt_i = build_salt_i(salt, i);
    let u1 = hmac_with_spec(password, &salt_i);
    proof {
        assert(u1@ == hmac_primitive_spec(password@, pbkdf2_salt_i_spec(salt@, i)));
        assert(u1@ == u_at_spec(password@, salt@, i, 1));
    }
    let mut t_i: [u8; 32] = u1;
    let mut u: [u8; 32] = u1;
    proof {
        let zero_t = t_xor_at_spec(password@, salt@, i, 0);
        assert(zero_t.len() == 32);
        let xor_with_zero = xor_seq_spec(zero_t, u1@);
        assert(xor_with_zero.len() == zero_t.len());
        assert forall|k: int| 0 <= k < 32 implies xor_with_zero[k] == u1@[k] by {
            assert(zero_t[k] == 0u8);
            lemma_xor_zero_u8(u1@[k]);
        }
        assert(xor_with_zero =~= u1@);
        assert(t_xor_at_spec(password@, salt@, i, 1) ==
               xor_seq_spec(t_xor_at_spec(password@, salt@, i, 0),
                            u_at_spec(password@, salt@, i, 1)));
        assert(t_i@ =~= t_xor_at_spec(password@, salt@, i, 1));
    }
    let mut j: u64 = 2;
    let iterations_u64: u64 = iterations as u64;
    while j <= iterations_u64
        invariant
            2 <= j <= iterations_u64 + 1,
            iterations_u64 == iterations as u64,
            password@.len() < 0x2000_0000u64,
            u@ == u_at_spec(password@, salt@, i, (j as int) - 1),
            t_i@ == t_xor_at_spec(password@, salt@, i, (j as int) - 1),
        decreases iterations_u64 - j + 1,
    {
        let u_next = hmac_with_spec(password, u.as_slice());
        proof {
            assert(u_next@ == hmac_primitive_spec(password@, u@));
            assert(u_next@ == u_at_spec(password@, salt@, i, j as int));
        }
        let mut new_t: [u8; 32] = [0u8; 32];
        let mut k: usize = 0;
        while k < 32
            invariant
                k <= 32,
                forall|m: int| 0 <= m < k as int ==> new_t@[m] == t_i@[m] ^ u_next@[m],
            decreases 32 - k,
        {
            new_t[k] = t_i[k] ^ u_next[k];
            k = k + 1;
        }
        proof {
            assert(new_t@ =~= xor_seq_spec(t_i@, u_next@));
            assert(new_t@ =~= t_xor_at_spec(password@, salt@, i, j as int));
        }
        t_i = new_t;
        u = u_next;
        j = j + 1;
    }
    t_i
}

// ── External-body top-level (block concatenation + truncation) ──────

#[verifier::external_body]
pub fn pbkdf2_hmac_sha256(
    password: &[u8],
    salt: &[u8],
    iterations: u32,
    dk_len: usize,
) -> (dk: Vec<u8>)
    requires
        iterations >= 1,
        dk_len <= 0x4000_0000usize,
        password@.len() < 0x2000_0000u64,
        salt@.len() < 0x1000_0000u64,
    ensures dk@ == pbkdf2_hmac_sha256_spec(password@, salt@,
        iterations as int, dk_len as int),
{
    let block_count = (dk_len + PBKDF2_HASH_BYTES - 1) / PBKDF2_HASH_BYTES;
    let mut dk: Vec<u8> = Vec::with_capacity(dk_len);
    let mut i: u32 = 1;
    while (i as usize) <= block_count {
        let t_i = pbkdf2_inner_chain(password, salt, iterations, i);
        let take = if (i as usize) == block_count {
            dk_len - ((i as usize) - 1) * PBKDF2_HASH_BYTES
        } else {
            PBKDF2_HASH_BYTES
        };
        for k in 0..take { dk.push(t_i[k]); }
        i = i + 1;
    }
    dk
}

}
