// Memoization composition pattern.
//
// Mirror of
// supplementary-research/studies/domain-corpora/algorithms/tla/compositions/MemoizationComposition.tla
// (TLC only; no TLAPS proof). The pattern: build up a key-value
// table by topological fill, each value computed from already-memoized
// predecessor values.
//
// The Verus version uses a simple chain-DAG (each key depends only
// on the immediately preceding key) so the topological order is the
// natural numeric order. Generalizing to arbitrary DAGs is
// straightforward but adds graph-machinery complexity beyond the scope
// of this module.

use vstd::prelude::*;

verus! {

pub const BASE_VAL: u64 = 1;
pub const STEP_VAL: u64 = 1;

/// Spec: f(k) = BASE_VAL + STEP_VAL * k (the linear recurrence after
/// filling a chain DAG of length k+1).
pub open spec fn abstract_val(k: int) -> int {
    BASE_VAL as int + STEP_VAL as int * k
}

/// Topological fill: memoize keys 0..n in order. memo[0] = BASE_VAL;
/// memo[k] = memo[k-1] + STEP_VAL.
pub fn memoize_chain(n: usize) -> (memo: Vec<u64>)
    requires n <= 1_000_000,
    ensures
        memo@.len() == n as int,
        forall|k: int| 0 <= k < n as int ==> memo@[k] == BASE_VAL + STEP_VAL * (k as u64),
{
    let mut memo: Vec<u64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n <= 1_000_000,
            memo@.len() == i as int,
            forall|k: int| 0 <= k < i as int
                ==> memo@[k] == BASE_VAL + STEP_VAL * (k as u64),
        decreases n - i,
    {
        let v: u64 = if i == 0 {
            BASE_VAL
        } else {
            // memo[i - 1] = BASE_VAL + STEP_VAL * (i - 1) <= 1_000_001
            assert(memo@[(i - 1) as int] == BASE_VAL + STEP_VAL * ((i - 1) as u64));
            memo[i - 1] + STEP_VAL
        };
        memo.push(v);
        i = i + 1;
    }
    memo
}

}
