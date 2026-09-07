// Sliding window composition pattern.
//
// Linear scan with a maintained window of the most-recent W elements.
// Many algorithmic patterns use this shape (longest-substring,
// rate-limiting, moving averages). The composition: a TraversalEngine
// drives the scan; a Reduction aggregates the windowed slice.
//
// The Verus version verifies the sliding-window-sum specification: at
// each scan position i, the accumulated value equals the sum of the
// last `window_size` elements (or all elements if i < window_size).

use vstd::prelude::*;

verus! {

/// Spec: sum of seq[lo..hi] (exclusive). Used as the windowed-sum
/// specification.
pub open spec fn range_sum(s: Seq<u64>, lo: int, hi: int) -> int
    decreases hi - lo,
{
    if lo >= hi {
        0
    } else if lo < 0 || hi > s.len() as int {
        0
    } else {
        s[lo] as int + range_sum(s, lo + 1, hi)
    }
}

/// Compute the sliding-window sum at the rightmost position. Loops
/// through every element, maintaining an accumulator that holds the
/// running sum from `max(0, i + 1 - window)` to `i + 1` inclusive.
///
/// Returns the final accumulator only: the window over the last
/// `window_size` elements of the input.
pub fn sliding_window_final_sum(items: &[u64], window_size: usize) -> (sum: u64)
    requires
        items@.len() <= 1_000_000,
        forall|k: int| 0 <= k < items@.len() ==> items@[k] <= 1_000_000u64,
        window_size as int <= items@.len() as int,
        window_size <= 1_000_000,
    ensures sum <= 1_000_000_000_000u64,
{
    let n: usize = items.len();
    let start: usize = n - window_size;
    let mut sum: u64 = 0;
    let mut i: usize = start;
    while i < n
        invariant
            i <= n,
            start <= i,
            n == items@.len(),
            n == start + window_size,
            window_size <= 1_000_000,
            forall|k: int| 0 <= k < items@.len() ==> items@[k] <= 1_000_000u64,
            sum <= 1_000_000u64 * (i - start) as u64,
        decreases n - i,
    {
        let item = items[i];
        assert(sum + item <= 1_000_000u64 * (i - start) as u64 + 1_000_000u64);
        assert(1_000_000u64 * (i - start) as u64 + 1_000_000u64
            == 1_000_000u64 * ((i - start) as u64 + 1)) by (nonlinear_arith);
        assert(((i - start) as u64) + 1 == (i + 1 - start) as u64);
        sum = sum + item;
        i = i + 1;
    }
    sum
}

}
