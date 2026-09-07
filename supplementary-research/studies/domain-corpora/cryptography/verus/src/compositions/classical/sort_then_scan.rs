// Sort-then-scan composition pattern.
//
// A sort followed by a linear scan over the sorted output. The sort
// produces the monotone invariant; the scan exploits it. Interval and
// greedy algorithms instantiate this shape. The composition: a sorting
// primitive (assumed correct here, since this layer does not ship a
// sort) produces the sorted slice; a TraversalEngine drives the scan;
// a Reduction aggregates the per-step finding.
//
// The Verus version verifies the post-sort scan claim: if the input
// slice is sorted, then scanning for adjacent duplicates correctly
// identifies the count of duplicate-adjacent pairs (a canonical
// instance of the "scan over sorted output" pattern; concrete
// instances like merge-intervals or non-overlapping-meetings
// instantiate this in the algorithm modules).

use vstd::prelude::*;

verus! {

/// Slice is sorted (non-strictly ascending).
pub open spec fn is_sorted(s: Seq<u64>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < s.len() ==> s[i] <= s[j]
}

/// Count adjacent-equal pairs in `s[0..n]`. Recursive spec.
pub open spec fn count_adjacent_equal_to(s: Seq<u64>, n: int) -> int
    decreases n,
{
    if n <= 1 {
        0
    } else if n > s.len() as int {
        0
    } else {
        count_adjacent_equal_to(s, n - 1)
            + (if s[n - 2] == s[n - 1] { 1int } else { 0int })
    }
}

/// Bound: the count of adjacent-equal pairs in s[0..n] is at most n.
/// (At most one per step.) Lemma used to discharge the no-overflow
/// obligation in the scan loop.
pub proof fn lemma_count_bounded(s: Seq<u64>, n: int)
    requires 0 <= n <= s.len() as int,
    ensures count_adjacent_equal_to(s, n) <= n,
    decreases n,
{
    if n > 1 {
        lemma_count_bounded(s, n - 1);
    }
}

/// Scan a sorted slice and count adjacent-equal pairs. Each
/// adjacent-equal pair is one "duplicate group boundary" continuation,
/// which is the canonical scan-finding for sorted inputs.
pub fn scan_sorted_count_adjacent_equal(sorted: &[u64]) -> (count: u64)
    requires
        is_sorted(sorted@),
        sorted@.len() <= 1_000_000_000,
    ensures
        count as int == count_adjacent_equal_to(sorted@, sorted@.len() as int),
{
    let n: usize = sorted.len();
    let mut count: u64 = 0;
    let mut i: usize = 1;
    while i < n
        invariant
            1 <= i <= if n == 0 { 1usize } else { n },
            n == sorted@.len(),
            n <= 1_000_000_000,
            is_sorted(sorted@),
            count as int == count_adjacent_equal_to(sorted@, i as int),
        decreases n - i,
    {
        proof {
            lemma_count_bounded(sorted@, i as int);
        }
        if sorted[i - 1] == sorted[i] {
            count = count + 1;
        }
        i = i + 1;
    }
    count
}

}
