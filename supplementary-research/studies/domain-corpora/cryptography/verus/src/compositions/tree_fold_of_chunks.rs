// TreeFoldOfChunks.
//
// BLAKE3's parallel-hashing pattern: chunks are
// hashed at the leaves, then pairs of chaining values are combined at
// each interior level via a compression function. The TLAPS proof at
// supplementary-research/studies/domain-corpora/cryptography/tla/compositions/TreeFoldOfChunks_Proof.tla closes 352
// obligations with the LevelLowerBound strengthening (level >= 1).
//
// For Verus, the natural model is a balanced binary tree-fold over an
// input slice whose length is a power of two. At level k, pair up
// adjacent values and apply the combiner. The recursion depth is
// log2(len).
//
// Verification boundary: written contracts plus named external-body assumptions.

use vstd::prelude::*;

verus! {

/// Compression of two chaining values (the BLAKE3 ParentChainingValue).
/// Concrete combiner: wrapping-XOR; AC-respecting like the TLA+ spec's
/// uninterpreted CompressionFn.
pub open spec fn compress_spec(left: u64, right: u64) -> u64 {
    left ^ right
}

pub fn compress(left: u64, right: u64) -> (r: u64)
    ensures r == compress_spec(left, right),
{
    left ^ right
}

/// One level of tree-fold: pair up adjacent elements of `level_input`
/// (which must have even length) and apply compress. The output has
/// half the length of the input.
pub fn fold_one_level(level_input: &Vec<u64>) -> (out: Vec<u64>)
    requires level_input@.len() % 2 == 0,
    ensures
        out@.len() == level_input@.len() / 2,
        forall|i: int| 0 <= i < out@.len()
            ==> out@[i] == compress_spec(level_input@[2 * i], level_input@[2 * i + 1]),
{
    let mut out: Vec<u64> = Vec::new();
    let n: usize = level_input.len();
    let mut i: usize = 0;
    while i < n / 2
        invariant
            n == level_input@.len(),
            n % 2 == 0,
            i <= n / 2,
            out@.len() == i as int,
            forall|j: int| 0 <= j < i as int
                ==> out@[j] == compress_spec(level_input@[2 * j], level_input@[2 * j + 1]),
        decreases n / 2 - i,
    {
        let l = level_input[2 * i];
        let r = level_input[2 * i + 1];
        out.push(compress(l, r));
        i = i + 1;
    }
    out
}

}
