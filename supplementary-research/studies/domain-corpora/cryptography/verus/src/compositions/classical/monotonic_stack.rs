// Monotonic-stack composition pattern.
//
// Mirror of
// supplementary-research/studies/domain-corpora/algorithms/tla/compositions/MonotonicStackComposition.tla
// (TLC only; no TLAPS proof). A stack whose contents are kept
// monotonically non-decreasing by popping any element greater than
// the incoming value before pushing. Used in next-greater-element,
// largest-rectangle-in-histogram, and many related algorithms.
//
// The Verus version maintains the monotonic invariant: the stack's
// values are non-decreasing from bottom to top. The push operation
// preserves this by popping out-of-order elements first.

use vstd::prelude::*;

verus! {

/// Stack invariant: values are non-decreasing from bottom to top.
pub open spec fn is_monotonic(s: Seq<u64>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < s.len() ==> s[i] <= s[j]
}

/// Monotonic push: pop any element greater than `v` from the top,
/// then push `v`. Preserves the monotonic invariant.
pub fn monotonic_push(stack: &mut Vec<u64>, v: u64)
    requires is_monotonic(old(stack)@),
    ensures
        is_monotonic(final(stack)@),
        // The pushed value is on top.
        final(stack)@.len() > 0,
        final(stack)@[final(stack)@.len() - 1] == v,
{
    // Pop while top > v.
    while stack.len() > 0 && stack[stack.len() - 1] > v
        invariant is_monotonic(stack@),
        decreases stack.len(),
    {
        stack.pop();
    }
    stack.push(v);
}

}
