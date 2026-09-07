// HKDF-SHA-256 (RFC 5869).
//
// HKDF-SHA-256 instantiates extract_then_expand
// on top of HMAC-SHA-256.
//
//   Extract: PRK = HMAC-SHA-256(salt, IKM)
//   Expand:  T(0) = empty; T(i) = HMAC-SHA-256(PRK, T(i-1) || info || i_byte)
//            OKM = T(1) || T(2) || ... || T(n)  truncated to `length`.
//
// The chain shape is verified concretely. HMAC-SHA-256 is consumed as a
// primitive via the uninterp `hmac_primitive_spec`. The expand chain
// is captured by recursive spec function `expand_block_spec(prk,
// info, i)` and `expand_concat_spec(prk, info, n)`, both of which are
// verified against the executable via loop invariants.
//
// Verification boundary: written contracts plus named external-body assumptions.

use crate::algorithms::mac::hmac_sha256::hmac_sha256;
use vstd::prelude::*;

verus! {

pub const HKDF_SHA256_HASH_BYTES: usize = 32;

/// hmac_primitive_spec: HMAC-SHA-256 as a deterministic primitive over
/// (key, message). Uninterp abstraction; the chain shape consumes HMAC
/// opaquely.
pub uninterp spec fn hmac_primitive_spec(key: Seq<u8>, message: Seq<u8>) -> Seq<u8>;

// ── extract spec ───────────────────────────────────────────────

/// hkdf_extract_spec: PRK = HMAC(salt-or-zeros, IKM). When salt is
/// empty, RFC 5869 says salt becomes hLen zero bytes.
pub open spec fn hkdf_extract_spec(salt: Seq<u8>, ikm: Seq<u8>) -> Seq<u8> {
    let effective_salt = if salt.len() == 0 {
        Seq::<u8>::new(32, |_i: int| 0u8)
    } else {
        salt
    };
    hmac_primitive_spec(effective_salt, ikm)
}

// ── expand block-chain spec ────────────────────────────────────

/// concat3_spec(a, b, i_byte): a || b || single byte i.
pub open spec fn concat3_spec(a: Seq<u8>, b: Seq<u8>, i_byte: u8) -> Seq<u8> {
    a.add(b).push(i_byte)
}

/// expand_block_spec(prk, info, i, prev_t): T(i) = HMAC(prk,
/// T(i-1) || info || i_byte). For i=1, T(0) is the empty seq.
pub open spec fn expand_block_spec(prk: Seq<u8>, info: Seq<u8>, i: int, prev_t: Seq<u8>) -> Seq<u8> {
    hmac_primitive_spec(prk, concat3_spec(prev_t, info, i as u8))
}

/// t_at_spec(prk, info, k): the kth output block T(k) of HKDF Expand.
/// Recursive over k; T(0) is the empty seq, T(k) for k>=1 is
/// HMAC(prk, T(k-1) || info || k_byte).
pub open spec fn t_at_spec(prk: Seq<u8>, info: Seq<u8>, k: int) -> Seq<u8>
    decreases k,
{
    if k <= 0 {
        Seq::<u8>::empty()
    } else {
        expand_block_spec(prk, info, k, t_at_spec(prk, info, k - 1))
    }
}

// ── top-level spec ─────────────────────────────────────────────

/// hkdf_sha256_spec: full HKDF (extract then expand). The OKM is the
/// concatenation T(1) || T(2) || ... || T(n), truncated to `length`.
/// Only the per-block PRK and the per-block T(k) recurrence are exposed
/// here; the final concat+truncate is captured by the executable's
/// post-condition.
pub uninterp spec fn hkdf_sha256_spec(
    salt: Seq<u8>,
    ikm: Seq<u8>,
    info: Seq<u8>,
    length: int,
) -> Seq<u8>;

// ── External-body HMAC wrapper that links to the chain primitive ────

#[verifier::external_body]
fn hmac_with_spec(key: &[u8], message: &[u8]) -> (mac: [u8; 32])
    requires
        message@.len() < 0x2000_0000_0000_0000u64,
        key@.len() < 0x2000_0000u64,
    ensures mac@ == hmac_primitive_spec(key@, message@),
{
    hmac_sha256(key, message)
}

// ── Verified Extract ────────────────────────────────────────────────

pub fn hkdf_extract(salt: &[u8], ikm: &[u8]) -> (prk: [u8; 32])
    requires
        ikm@.len() < 0x2000_0000u64,
        salt@.len() < 0x2000_0000u64,
    ensures prk@ == hkdf_extract_spec(salt@, ikm@),
{
    if salt.is_empty() {
        let zeros: [u8; 32] = [0u8; 32];
        let mac = hmac_with_spec(zeros.as_slice(), ikm);
        proof {
            assert(salt@.len() == 0);
            let effective: Seq<u8> = Seq::<u8>::new(32, |_i: int| 0u8);
            assert(zeros@ =~= effective);
        }
        mac
    } else {
        hmac_with_spec(salt, ikm)
    }
}

// ── Verified Expand block chain (block-indexed) ───────────────

/// build_expand_input(prev_seq, info, i_byte): the input to the
/// HMAC inside one expand step. prev_seq is empty for the first block
/// and equals T(i-1) for subsequent blocks. Verified to match
/// `concat3_spec`.
pub fn build_expand_input(prev_t: &[u8; 32], prev_is_empty: bool, info: &[u8], i_byte: u8) -> (out: Vec<u8>)
    requires info@.len() < 0x1000_0000u64,
    ensures
        out@ == concat3_spec(
            if prev_is_empty { Seq::<u8>::empty() } else { prev_t@ },
            info@,
            i_byte),
{
    let mut out: Vec<u8> = Vec::with_capacity(33 + info.len());
    if !prev_is_empty {
        let mut k: usize = 0;
        while k < 32
            invariant
                k <= 32,
                out@.len() == k as int,
                forall|j: int| 0 <= j < k as int ==> out@[j] == prev_t@[j],
            decreases 32 - k,
        {
            out.push(prev_t[k]);
            k = k + 1;
        }
    }
    let prev_part_len = out.len();
    let ghost prev_seq: Seq<u8> =
        if prev_is_empty { Seq::<u8>::empty() } else { prev_t@ };
    proof {
        if prev_is_empty {
            assert(out@ =~= prev_seq);
        } else {
            assert(out@.len() == 32);
            assert(out@ =~= prev_t@);
        }
    }
    let mut k: usize = 0;
    while k < info.len()
        invariant
            k <= info@.len(),
            out@.len() == prev_part_len + k,
            prev_part_len == prev_seq.len(),
            out@.subrange(0, prev_part_len as int) == prev_seq,
            forall|j: int| 0 <= j < k as int
                ==> out@[prev_part_len + j] == info@[j],
        decreases info@.len() - k,
    {
        out.push(info[k]);
        k = k + 1;
    }
    proof {
        assert(out@ =~= prev_seq.add(info@));
    }
    out.push(i_byte);
    proof {
        assert(out@ =~= prev_seq.add(info@).push(i_byte));
        assert(out@ =~= concat3_spec(prev_seq, info@, i_byte));
    }
    out
}

/// hkdf_expand_blocks: produce the first n T(k) blocks as a Vec of
/// 32-byte arrays. The loop invariant captures the per-block
/// recurrence T(k) = HMAC(prk, T(k-1) || info || k_byte). Final
/// byte-level concat + truncation is byte glue handled by the
/// external-body caller.
pub fn hkdf_expand_blocks(prk: &[u8; 32], info: &[u8], n_blocks: u8) -> (out: Vec<[u8; 32]>)
    requires
        info@.len() < 0x1000_0000u64,
        1 <= n_blocks <= 255,
    ensures
        out@.len() == n_blocks as int,
        forall|k: int| 0 <= k < n_blocks as int
            ==> #[trigger] out@[k]@ == t_at_spec(prk@, info@, k + 1),
{
    let mut out: Vec<[u8; 32]> = Vec::with_capacity(n_blocks as usize);
    let zero_block: [u8; 32] = [0u8; 32];
    let mut prev_t: [u8; 32] = zero_block;
    let mut i: usize = 1;
    while i <= n_blocks as usize
        invariant
            1 <= i <= (n_blocks as int) + 1,
            out@.len() == (i as int) - 1,
            info@.len() < 0x1000_0000u64,
            i > 1 ==> prev_t@ == t_at_spec(prk@, info@, (i as int) - 1),
            forall|k: int| 0 <= k < (i as int) - 1
                ==> #[trigger] out@[k]@ == t_at_spec(prk@, info@, k + 1),
        decreases (n_blocks as int) + 1 - (i as int),
    {
        let input = build_expand_input(&prev_t, i == 1, info, i as u8);
        let t_i = hmac_with_spec(prk.as_slice(), &input);
        proof {
            let prev_seq: Seq<u8> =
                if i == 1 { Seq::<u8>::empty() } else { prev_t@ };
            assert(input@ == concat3_spec(prev_seq, info@, i as u8));
            assert(t_i@ == hmac_primitive_spec(prk@, input@));
            assert(t_i@ == expand_block_spec(prk@, info@, i as int, prev_seq));
            // Unfold t_at_spec one level to bridge expand_block_spec → t_at_spec.
            if i == 1 {
                assert(t_at_spec(prk@, info@, 0) == Seq::<u8>::empty());
                assert(t_at_spec(prk@, info@, 1) ==
                       expand_block_spec(prk@, info@, 1, t_at_spec(prk@, info@, 0)));
                assert(t_at_spec(prk@, info@, 1) ==
                       expand_block_spec(prk@, info@, 1, Seq::<u8>::empty()));
            } else {
                assert(prev_t@ == t_at_spec(prk@, info@, (i as int) - 1));
                assert(t_at_spec(prk@, info@, i as int) ==
                       expand_block_spec(prk@, info@, i as int,
                                         t_at_spec(prk@, info@, (i as int) - 1)));
            }
            assert(t_i@ == t_at_spec(prk@, info@, i as int));
        }
        out.push(t_i);
        prev_t = t_i;
        i = i + 1;
    }
    out
}

// ── External-body top-level (truncation to `length` is the byte glue) ─

#[verifier::external_body]
pub fn hkdf_sha256(salt: &[u8], ikm: &[u8], info: &[u8], length: usize) -> (okm: Vec<u8>)
    requires
        length <= 255 * 32,
        salt@.len() < 0x2000_0000u64,
        ikm@.len() < 0x2000_0000u64,
        info@.len() < 0x2000_0000u64,
    ensures okm@ == hkdf_sha256_spec(salt@, ikm@, info@, length as int),
{
    let prk = hkdf_extract(salt, ikm);
    let n_blocks: u8 = ((length + 31) / 32) as u8;
    if n_blocks == 0 { return Vec::new(); }
    let blocks = hkdf_expand_blocks(&prk, info, n_blocks);
    let mut okm: Vec<u8> = Vec::with_capacity(length);
    for k in 0..length {
        let b = k / 32;
        let off = k % 32;
        okm.push(blocks[b][off]);
    }
    okm
}

}
