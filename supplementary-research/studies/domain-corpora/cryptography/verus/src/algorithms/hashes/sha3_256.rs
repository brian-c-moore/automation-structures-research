// SHA-3-256.
//
// SHA-3-256 instantiates absorb_then_squeeze
// with the Keccak-f[1600] permutation as the round content. State =
// 25 × u64 lanes (1600 bits); rate = 17 lanes (1088 bits); capacity =
// 8 lanes (512 bits); pad10*1 with FIPS 202 §B.2 domain separator
// 0x06; output = first 32 bytes of the state after the final permute
// (single squeeze; 4 lanes < rate, so no inter-squeeze permute).
//
// Under the hybrid composition heuristic this module is self-contained:
// SHA-3-256's state shape (25-lane Seq<u64>) and its permutation
// (Keccak-f[1600]'s 24-round θρπχι) differ from the base composition's
// u64 state and simple AC permute. The chain pattern is the structural
// model; the implementation is re-derived inline for the concrete shape.
//
// Verification scope. The Keccak-f[1600] permutation is 24 rounds × 5
// steps × 25 lanes of bit-level XOR/AND/NOT/rotate operations. Inlining
// the full FIPS 202 §3.2 spec functionally is tractable but SMT-heavy;
// the SHA-3-256 verification target is therefore the structural shape
// (xor-into-rate followed by permutation), with the
// permutation modeled by an uninterp spec function `keccak_perm_spec`.
// The concrete FIPS 202 §3.2 round content (KECCAK_RHO, KECCAK_RC,
// theta/rho/pi/chi/iota) is implemented in the external-body
// `keccak_f1600` exec function and validated extrinsically by NIST
// CAVP KAT vectors (see tests/sha3_256_kat.rs).
//
// TLAPS reference: supplementary-research/studies/domain-corpora/cryptography/tla/compositions/AbsorbThenSqueeze_Proof.tla
// (283 obligations cold-deterministic). The Verus translation reuses
// the base module's chain shape with the algorithm-specific state
// width (25 lanes vs. 1 u64) and rate (17 lanes vs. 1 lane).
//
// Verification boundary: written contracts plus named external-body assumptions.

use vstd::prelude::*;

verus! {

// ── FIPS 202 §3.2 constants ──────────────────────────────────────────

/// Keccak-f[1600] rotation offsets ρ[x, y], flat-indexed as `x + 5*y`.
/// All values are mod 64. (FIPS 202 §3.2.2, Table 2.)
pub const KECCAK_RHO: [u32; 25] = [
    0,  1, 62, 28, 27,
    36, 44,  6, 55, 20,
     3, 10, 43, 25, 39,
    41, 45, 15, 21,  8,
    18,  2, 61, 56, 14,
];

/// Keccak-f[1600] round constants RC[0..24]. (FIPS 202 §3.2.5, Table 1.)
pub const KECCAK_RC: [u64; 24] = [
    0x0000000000000001, 0x0000000000008082, 0x800000000000808a, 0x8000000080008000,
    0x000000000000808b, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
    0x000000000000008a, 0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
    0x000000008000808b, 0x800000000000008b, 0x8000000000008089, 0x8000000000008003,
    0x8000000000008002, 0x8000000000000080, 0x000000000000800a, 0x800000008000000a,
    0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
];

/// State width (5 × 5 lanes).
pub const STATE_LANES: usize = 25;

/// SHA-3-256 rate (in 64-bit lanes). 1088-bit rate / 64 bits per lane = 17.
pub const SHA3_256_RATE_LANES: usize = 17;

/// SHA-3-256 rate (in bytes). 1088 / 8 = 136 bytes per block.
pub const SHA3_256_RATE_BYTES: usize = 136;

/// SHA-3 multi-rate domain suffix (FIPS 202 §B.2).
pub const SHA3_DOMAIN_SUFFIX: u8 = 0x06;

// ── Uninterpreted Keccak-f[1600] spec ────────────────────────────────

/// keccak_perm_spec: the Keccak-f[1600] permutation, modeled as an
/// uninterpreted deterministic function over 25-lane Seq<u64>. The
/// structural correctness of the absorb-then-squeeze chain
/// depends only on the permutation being deterministic, which an
/// uninterp spec function guarantees by definition.
///
/// The concrete FIPS 202 §3.2 round content is implemented in the
/// external-body `keccak_f1600` exec function and validated by NIST
/// CAVP KAT vectors (tests/sha3_256_kat.rs).
pub uninterp spec fn keccak_perm_spec(state: Seq<u64>) -> Seq<u64>;

// ── XOR-into-rate spec ───────────────────────────────────────────────

/// xor_into_rate_spec(state, block): the result of XORing the 17-lane
/// block into the first 17 lanes of the 25-lane state (the rate
/// portion); the last 8 lanes (the capacity portion) are unchanged.
/// FIPS 202 §B.1.
pub open spec fn xor_into_rate_spec(state: Seq<u64>, block: Seq<u64>) -> Seq<u64> {
    Seq::<u64>::new(25, |i: int| {
        if 0 <= i < 17 {
            state[i] ^ block[i]
        } else {
            state[i]
        }
    })
}

// ── absorb_one_spec: XOR-into-rate then permute ────────────────

/// absorb_one_spec(state, block): the "absorb one block" step
/// for SHA-3-256. XORs the 17 rate lanes from block into state, then
/// applies Keccak-f[1600] to the entire 25-lane state.
pub open spec fn absorb_one_spec(state: Seq<u64>, block: Seq<u64>) -> Seq<u64> {
    keccak_perm_spec(xor_into_rate_spec(state, block))
}

// ── Executable Keccak-f[1600] ───────────────────────────────────────

/// keccak_f1600: 24 rounds of θ ρ π χ ι applied in place to the
/// 25-lane state. Marked external_body; the concrete FIPS 202 §3.2
/// round content is validated extrinsically via NIST CAVP KAT vectors.
/// The ensures clause links the executable to the uninterp spec.
#[verifier::external_body]
pub fn keccak_f1600(state: &mut [u64; 25])
    ensures final(state)@ == keccak_perm_spec(old(state)@),
{
    for round in 0..24 {
        // θ: column-parity diffusion.
        let mut c = [0u64; 5];
        for x in 0..5 {
            c[x] = state[x] ^ state[x + 5] ^ state[x + 10] ^ state[x + 15] ^ state[x + 20];
        }
        let mut d = [0u64; 5];
        for x in 0..5 {
            d[x] = c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1);
        }
        for y in 0..5 {
            for x in 0..5 {
                state[x + 5 * y] ^= d[x];
            }
        }

        // ρ + π fused: rotate each lane by KECCAK_RHO[src] and permute
        // to position (x, y) per new[x,y] = old[(x+3y) mod 5, x].
        let mut tmp = [0u64; 25];
        for x in 0..5 {
            for y in 0..5 {
                let src_x = (x + 3 * y) % 5;
                let src_y = x;
                let src = src_x + 5 * src_y;
                tmp[x + 5 * y] = state[src].rotate_left(KECCAK_RHO[src]);
            }
        }
        *state = tmp;

        // χ: nonlinear row mixing.
        let snap = *state;
        for y in 0..5 {
            for x in 0..5 {
                state[x + 5 * y] = snap[x + 5 * y]
                    ^ ((!snap[(x + 1) % 5 + 5 * y]) & snap[(x + 2) % 5 + 5 * y]);
            }
        }

        // ι: XOR round constant into lane 0.
        state[0] ^= KECCAK_RC[round];
    }
}

// ── Executable absorb_one (verified) ────────────────────────────────

/// absorb_one(state, block): XOR the 17 rate lanes from block into
/// state[0..17], then apply Keccak-f[1600]. The ensures clause closes
/// the chain pattern in concrete form for SHA-3-256.
pub fn absorb_one(state: &mut [u64; 25], block: &[u64; 17])
    ensures
        final(state)@ == absorb_one_spec(old(state)@, block@),
{
    let mut i: usize = 0;
    while i < 17
        invariant
            i <= 17,
            forall|j: int| 0 <= j < i as int ==> state@[j] == (old(state)@[j] ^ block@[j as int]),
            forall|j: int| i as int <= j < 25 ==> state@[j] == old(state)@[j],
        decreases 17 - i,
    {
        let cur = state[i];
        let new_val = cur ^ block[i];
        state[i] = new_val;
        i = i + 1;
    }
    proof {
        assert(state@ =~= xor_into_rate_spec(old(state)@, block@));
    }
    keccak_f1600(state);
}

// ── absorb_all_spec: chain over a block sequence ───────────────

/// absorb_all_spec: the "absorb all blocks" chain for SHA-3-256.
/// Recursive over the count n; mirrors absorb_then_squeeze::absorb_all_spec
/// from the base module, with the state shape and block shape extended.
pub open spec fn absorb_all_spec(
    state: Seq<u64>,
    blocks: Seq<Seq<u64>>,
    n: int,
) -> Seq<u64>
    decreases n,
{
    if n <= 0 {
        state
    } else if n > blocks.len() as int {
        state
    } else {
        absorb_one_spec(absorb_all_spec(state, blocks, n - 1), blocks[n - 1])
    }
}

// ── Executable absorb_all (verified) ────────────────────────────────

/// absorb_all(state, blocks): iterate `absorb_one` over the sequence
/// of 17-lane blocks. The ensures clause closes the chain in
/// fully concrete form.
pub fn absorb_all(state: &mut [u64; 25], blocks: &[[u64; 17]])
    ensures
        final(state)@ == absorb_all_spec(
            old(state)@,
            Seq::<Seq<u64>>::new(blocks@.len(), |k: int| blocks@[k]@),
            blocks@.len() as int,
        ),
{
    let ghost initial = old(state)@;
    let ghost block_seqs = Seq::<Seq<u64>>::new(blocks@.len(), |k: int| blocks@[k]@);
    let n = blocks.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == blocks@.len(),
            block_seqs == Seq::<Seq<u64>>::new(blocks@.len(), |k: int| blocks@[k]@),
            state@ == absorb_all_spec(initial, block_seqs, i as int),
        decreases n - i,
    {
        absorb_one(state, &blocks[i]);
        proof {
            assert(block_seqs[i as int] == blocks@[i as int]@);
        }
        i = i + 1;
    }
}

// ── Full SHA-3-256 (external_body) ──────────────────────────────────

/// sha3_256: full FIPS 202 SHA-3-256. Pads with pad10*1 +
/// domain-separator 0x06, absorbs at 1088-bit rate, applies the final
/// permute, and squeezes 32 bytes (4 lanes) little-endian.
///
/// Marked external_body: the byte-level glue (length-based block
/// counts, pad10*1 padding, little-endian lane packing, partial
/// squeeze) is mechanical. Structural correctness comes from the
/// verified `absorb_all` + `absorb_one`. End-to-end correctness is
/// validated by tests/sha3_256_kat.rs against NIST CAVP vectors.
#[verifier::external_body]
pub fn sha3_256(msg: &[u8]) -> (digest: [u8; 32])
    requires msg@.len() < 0x2000_0000_0000_0000u64,
{
    let mut state = [0u64; 25];

    let full_blocks = msg.len() / SHA3_256_RATE_BYTES;
    for b in 0..full_blocks {
        let off = b * SHA3_256_RATE_BYTES;
        let mut block_lanes = [0u64; 17];
        for j in 0..17 {
            block_lanes[j] = u64::from_le_bytes([
                msg[off + j * 8],
                msg[off + j * 8 + 1],
                msg[off + j * 8 + 2],
                msg[off + j * 8 + 3],
                msg[off + j * 8 + 4],
                msg[off + j * 8 + 5],
                msg[off + j * 8 + 6],
                msg[off + j * 8 + 7],
            ]);
        }
        absorb_one(&mut state, &block_lanes);
    }

    let tail_start = full_blocks * SHA3_256_RATE_BYTES;
    let tail_len = msg.len() - tail_start;
    let mut last = [0u8; SHA3_256_RATE_BYTES];
    for k in 0..tail_len {
        last[k] = msg[tail_start + k];
    }
    last[tail_len] = SHA3_DOMAIN_SUFFIX;
    last[SHA3_256_RATE_BYTES - 1] |= 0x80;

    let mut last_lanes = [0u64; 17];
    for j in 0..17 {
        last_lanes[j] = u64::from_le_bytes([
            last[j * 8],
            last[j * 8 + 1],
            last[j * 8 + 2],
            last[j * 8 + 3],
            last[j * 8 + 4],
            last[j * 8 + 5],
            last[j * 8 + 6],
            last[j * 8 + 7],
        ]);
    }
    absorb_one(&mut state, &last_lanes);

    let mut out = [0u8; 32];
    for j in 0..4 {
        let lane_bytes = state[j].to_le_bytes();
        out[j * 8] = lane_bytes[0];
        out[j * 8 + 1] = lane_bytes[1];
        out[j * 8 + 2] = lane_bytes[2];
        out[j * 8 + 3] = lane_bytes[3];
        out[j * 8 + 4] = lane_bytes[4];
        out[j * 8 + 5] = lane_bytes[5];
        out[j * 8 + 6] = lane_bytes[6];
        out[j * 8 + 7] = lane_bytes[7];
    }
    out
}

}
