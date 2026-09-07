// SIMD-lane-batched refinement: N lanes parallel to sequential
// invocations produce equivalent per-lane output.
//
// TLAPS reference: supplementary-research/studies/domain-corpora/cryptography/tla/realizations/SimdLaneBatchedRefinesBase_Proof.tla
// (89 obligations).

use vstd::prelude::*;

verus! {

pub const N_LANES: usize = 4;
pub const M: u64 = 16;

pub fn simd_refinement(rounds: u64) -> (out: (Vec<u64>, Vec<u64>))
    requires rounds <= 16,
    ensures
        out.0@.len() == N_LANES as int,
        out.1@.len() == N_LANES as int,
        forall|k: int| 0 <= k < N_LANES as int ==> out.0@[k] == out.1@[k],
{
    let mut base: Vec<u64> = Vec::new();
    let mut simd: Vec<u64> = Vec::new();
    let mut k: usize = 0;
    while k < N_LANES
        invariant
            k <= N_LANES,
            base@.len() == k as int,
            simd@.len() == k as int,
            forall|j: int| 0 <= j < k as int ==> base@[j] < M,
            forall|j: int| 0 <= j < k as int ==> simd@[j] < M,
            forall|j: int| 0 <= j < k as int ==> base@[j] == simd@[j],
        decreases N_LANES - k,
    {
        base.push(k as u64);
        simd.push(k as u64);
        k = k + 1;
    }

    let mut r: u64 = 0;
    while r < rounds
        invariant
            r <= rounds,
            rounds <= 16,
            base@.len() == N_LANES as int,
            simd@.len() == N_LANES as int,
            forall|k: int| 0 <= k < N_LANES as int ==> base@[k] < M,
            forall|k: int| 0 <= k < N_LANES as int ==> simd@[k] < M,
            forall|k: int| 0 <= k < N_LANES as int ==> base@[k] == simd@[k],
        decreases rounds - r,
    {
        let mut k2: usize = 0;
        while k2 < N_LANES
            invariant
                k2 <= N_LANES,
                r < rounds,
                rounds <= 16,
                base@.len() == N_LANES as int,
                simd@.len() == N_LANES as int,
                forall|k: int| 0 <= k < N_LANES as int ==> base@[k] < M,
                forall|k: int| 0 <= k < N_LANES as int ==> simd@[k] < M,
                forall|k: int| 0 <= k < N_LANES as int ==> base@[k] == simd@[k],
            decreases N_LANES - k2,
        {
            let b = (base[k2] + r + 1) % M;
            let s = (simd[k2] + r + 1) % M;
            base.set(k2, b);
            simd.set(k2, s);
            k2 = k2 + 1;
        }
        r = r + 1;
    }
    (base, simd)
}

}
