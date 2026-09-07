// Priority-driven propagation composition pattern.
//
// CompetitiveSelection + PropagationPass: at each step, pick the
// next-best candidate per a comparator, then propagate the update.
// Used in Dijkstra, Prim, Huffman, A*, and many priority-driven
// algorithms. The composition: a comparator-priority primitive
// (modeled here as min-extract) drives the selection; a
// ResourceRegistry holds the per-node distance state; a TraversalEngine
// drives the propagation pass.
//
// The Verus version verifies the basic min-extraction shape: given
// a slice of u64 distance values, find the minimum value's index.
// Per-edge relaxation is the natural instantiation for full Dijkstra;
// the Verus layer covers only the extract-min primitive, which is the
// unique algorithmic shape of priority-driven propagation.

use vstd::prelude::*;

verus! {

/// Spec: returned index points at a minimum entry.
pub open spec fn is_min_index(s: Seq<u64>, idx: int) -> bool {
    0 <= idx < s.len()
    && forall|k: int| 0 <= k < s.len() ==> s[idx] <= s[k]
}

/// Extract the index of a minimum value. Returns 0 if the slice is
/// empty (defensive default; precondition rules this out for callers
/// that need the min-index guarantee).
pub fn extract_min_index(values: &[u64]) -> (idx: usize)
    requires values@.len() > 0,
    ensures
        (idx as int) < values@.len() as int,
        is_min_index(values@, idx as int),
{
    let n: usize = values.len();
    let mut best: usize = 0;
    let mut best_val: u64 = values[0];
    let mut i: usize = 1;
    while i < n
        invariant
            best < n,
            i <= n,
            n == values@.len(),
            best_val == values@[best as int],
            forall|k: int| 0 <= k < i as int ==> values@[k] >= best_val,
        decreases n - i,
    {
        let v = values[i];
        if v < best_val {
            best = i;
            best_val = v;
        }
        i = i + 1;
    }
    best
}

}
