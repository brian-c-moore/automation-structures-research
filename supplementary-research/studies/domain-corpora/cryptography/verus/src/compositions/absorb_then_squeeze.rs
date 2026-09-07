// AbsorbThenSqueeze (sponge).
//
// SHA-3's two-phase sponge construction:
//   Absorb:  for each input block, state = permute(state XOR block).
//   Squeeze: emit state as output, permute, repeat until enough output.
//
// The TLAPS proof at supplementary-research/studies/domain-corpora/cryptography/tla/compositions/
// AbsorbThenSqueeze_Proof.tla closes 283 obligations with the
// OutputsTrackSqueezeIdx strengthening (Len(outputs) = squeeze_idx - 1).
//
// For Verus, the two-phase shape becomes:
//   absorb_all(state, blocks) -> state'  (after absorbing all blocks)
//   squeeze_n(state, n) -> Vec<u64>     (n output words)
//   sponge(blocks, output_len) = squeeze_n(absorb_all(state0, blocks), output_len)
//
// Permute is the uninterpreted permutation; instantiated per algorithm
// (Keccak-f[1600] for SHA-3) in the algorithm modules.
//
// Verification boundary: written contracts plus named external-body assumptions.

use vstd::prelude::*;

verus! {

/// The sponge permutation: concrete operator for structural verification
/// (wrapping byte-rotate combined with XOR-with-constant; AC-respecting
/// but not the actual Keccak-f). Algorithm-specific permutations
/// instantiate this in the algorithm modules.
pub open spec fn permute_spec(s: u64) -> u64 {
    s.wrapping_mul(0x9E3779B97F4A7C15u64)
        ^ s.wrapping_shr(13)
}

pub fn permute(s: u64) -> (r: u64)
    ensures r == permute_spec(s),
{
    s.wrapping_mul(0x9E3779B97F4A7C15u64)
        ^ s.wrapping_shr(13)
}

/// Absorb one input block into the state: XOR-then-permute. The TLA+
/// spec calls this AbsorbBlock.
pub open spec fn absorb_one_spec(state: u64, block: u64) -> u64 {
    permute_spec(state ^ block)
}

pub fn absorb_one(state: u64, block: u64) -> (r: u64)
    ensures r == absorb_one_spec(state, block),
{
    permute(state ^ block)
}

/// Absorb all blocks in order. The mathematical fold; spec function
/// is recursive over the block sequence's prefix length.
pub open spec fn absorb_all_spec(state: u64, blocks: Seq<u64>, n: int) -> u64
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

pub fn absorb_all(initial: u64, blocks: &[u64]) -> (r: u64)
    ensures r == absorb_all_spec(initial, blocks@, blocks@.len() as int),
{
    let n: usize = blocks.len();
    let mut state: u64 = initial;
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == blocks@.len(),
            state == absorb_all_spec(initial, blocks@, i as int),
        decreases n - i,
    {
        state = absorb_one(state, blocks[i]);
        i = i + 1;
    }
    state
}

/// Squeeze n output blocks from the state. Each squeeze emits the
/// current state and applies the permutation; the sequence captures
/// OutputsTrackSqueezeIdx (the length of outputs equals the number of
/// squeezes performed).
pub fn squeeze_n(initial: u64, n: usize) -> (out: Vec<u64>)
    ensures out@.len() == n as int,
{
    let mut out: Vec<u64> = Vec::new();
    let mut state: u64 = initial;
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            out@.len() == i as int,
        decreases n - i,
    {
        out.push(state);
        state = permute(state);
        i = i + 1;
    }
    out
}

}
