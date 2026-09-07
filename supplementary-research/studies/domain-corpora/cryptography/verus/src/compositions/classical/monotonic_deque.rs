// Monotonic-deque composition pattern (companion to monotonic_stack).
//
// Mirror of
// supplementary-research/studies/domain-corpora/algorithms/tla/compositions/MonotonicDequeComposition.tla.
// A deque whose values are monotonically non-increasing front-to-back,
// supporting push to back (with pop-back of larger values) and pop
// from front. Used in sliding-window-maximum and related algorithms.
//
// The Verus version maintains the monotonic-decreasing invariant: the
// deque's values are non-increasing from front (index 0) to back
// (index len-1).

use vstd::prelude::*;

verus! {

/// Deque invariant: values non-increasing from front to back.
pub open spec fn is_monotonic_decreasing(s: Seq<u64>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < s.len() ==> s[i] >= s[j]
}

/// Monotonic push-back: pop any back element smaller than `v`, then
/// push `v`. Preserves the non-increasing invariant.
pub fn monotonic_push_back(dq: &mut Vec<u64>, v: u64)
    requires is_monotonic_decreasing(old(dq)@),
    ensures
        is_monotonic_decreasing(final(dq)@),
        final(dq)@.len() > 0,
        final(dq)@[final(dq)@.len() - 1] == v,
{
    while dq.len() > 0 && dq[dq.len() - 1] < v
        invariant is_monotonic_decreasing(dq@),
        decreases dq.len(),
    {
        dq.pop();
    }
    dq.push(v);
}

}
