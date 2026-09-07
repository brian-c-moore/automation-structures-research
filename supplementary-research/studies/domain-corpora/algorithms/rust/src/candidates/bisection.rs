//! **Bisection**.
//!
//! **Motivation.** Given an ordered domain and a monotonic predicate,
//! the optimal search halves the domain per probe.
//!
//! **Definition.** Ordered domain `D`, monotonic predicate `P` (false
//! then true exactly once). Find the threshold by halving.
//!
//! **Invariant.** Halving: each probe shrinks the candidate range by ≥
//! a factor of two. Soundness needs `P` monotonic.
//!
//! **Recognition.** Binary search over indices, parametric "search on
//! the answer", `Pow(x,n)` over exponent bits, root finding.

pub struct Bisection;

impl Bisection {
    /// Smallest integer `x` in `[lo, hi]` with `pred(x) == true`,
    /// assuming `pred` is monotonic (false…false,true…true) over the
    /// range; returns `hi + 1`-style sentinel via `None` if never true.
    pub fn first_true<F: Fn(i64) -> bool>(mut lo: i64, mut hi: i64, pred: F) -> Option<i64> {
        let mut ans = None;
        while lo <= hi {
            let mid = lo + (hi - lo) / 2; // halving probe
            if pred(mid) {
                ans = Some(mid);
                hi = mid - 1;
            } else {
                lo = mid + 1;
            }
        }
        ans
    }

    /// Classic value search: index of `target` in a sorted slice, or
    /// `None`. (Bisection with the three-valued comparison predicate.)
    pub fn search<T: Ord>(sorted: &[T], target: &T) -> Option<usize> {
        let (mut lo, mut hi) = (0i64, sorted.len() as i64 - 1);
        while lo <= hi {
            let mid = (lo + (hi - lo) / 2) as usize;
            match sorted[mid].cmp(target) {
                std::cmp::Ordering::Equal => return Some(mid),
                std::cmp::Ordering::Less => lo = mid as i64 + 1,
                std::cmp::Ordering::Greater => hi = mid as i64 - 1,
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn search_finds_and_misses() {
        let a = [1, 3, 5, 7, 9];
        assert_eq!(Bisection::search(&a, &7), Some(3));
        assert_eq!(Bisection::search(&a, &4), None);
    }
    #[test]
    fn first_true_threshold() {
        // predicate: x*x >= 16  -> threshold at 4
        assert_eq!(Bisection::first_true(0, 100, |x| x * x >= 16), Some(4));
    }
}
