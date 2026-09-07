//! The algorithm corpus, one fn per algorithm, built **only** from
//! [`crate::primitives`] and [`crate::candidates`]; algorithms reuse
//! those definitions instead of reimplementing primitive logic.
//!
//! The corpus phases are: 1 DP, 2 stack plus binary search, 3 advanced
//! graphs, 4 backtracking, 5 trees + heap, 6 arrays/two-pointer/
//! sliding-window, 7 linked-list/tries/graphs, 8 greedy/intervals/
//! math/bit.

use crate::config::CorpusEntry;
use crate::value::Value;

pub mod phase1_dp;
pub mod phase2_stack_bsearch;
pub mod phase3_adv_graphs;
pub mod phase4_backtracking;
pub mod phase5_trees_heap;
pub mod phase6_arrays;
pub mod phase7_lists_tries_graphs;
pub mod phase8_greedy_intervals_math_bit;

/// Concatenate every phase's entries at one aggregation point.
pub fn registry() -> Vec<CorpusEntry> {
    let mut r = Vec::new();
    phase1_dp::add(&mut r);
    phase2_stack_bsearch::add(&mut r);
    phase3_adv_graphs::add(&mut r);
    phase4_backtracking::add(&mut r);
    phase5_trees_heap::add(&mut r);
    phase6_arrays::add(&mut r);
    phase7_lists_tries_graphs::add(&mut r);
    phase8_greedy_intervals_math_bit::add(&mut r);
    r
}

/// Shared input generation:
/// curated edge cases plus deterministic property-based inputs. Reused
/// by every phase module.
pub mod gen {
    use crate::primitives::Sampler;
    use crate::value::Value;

    /// `count` deterministic pseudo-random integer lists, each of length
    /// `0..=max_len`, values in `lo..=hi`.
    pub fn rand_int_lists(seed: u64, count: usize, max_len: usize, lo: i64, hi: i64) -> Vec<Value> {
        let mut s = Sampler::new(seed);
        let span = (hi - lo + 1).max(1) as usize;
        (0..count)
            .map(|_| {
                let len = s.pick_index(max_len + 1);
                Value::List(
                    (0..len)
                        .map(|_| Value::Int(lo + s.pick_index(span) as i64))
                        .collect(),
                )
            })
            .collect()
    }

    /// `count` deterministic pseudo-random non-negative integers in
    /// `0..=hi`.
    pub fn rand_ints(seed: u64, count: usize, hi: i64) -> Vec<Value> {
        let mut s = Sampler::new(seed);
        let span = (hi + 1).max(1) as usize;
        (0..count)
            .map(|_| Value::Int(s.pick_index(span) as i64))
            .collect()
    }

    /// `count` deterministic pseudo-random lowercase strings of length
    /// `0..=max_len` over an alphabet of size `alpha` (a..).
    pub fn rand_strings(seed: u64, count: usize, max_len: usize, alpha: usize) -> Vec<Value> {
        let mut s = Sampler::new(seed);
        (0..count)
            .map(|_| {
                let len = s.pick_index(max_len + 1);
                let st: String = (0..len)
                    .map(|_| (b'a' + s.pick_index(alpha) as u8) as char)
                    .collect();
                Value::Str(st)
            })
            .collect()
    }
}

/// Shared per-phase helper for constructing registry entries.
#[allow(clippy::too_many_arguments)]
pub fn entry(
    r: &mut Vec<CorpusEntry>,
    name: &'static str,
    category: &'static str,
    phase: u8,
    ordering: &'static str,
    primitives: &'static str,
    compose: fn(Value) -> Value,
    oracle: &'static str,
    equiv: crate::equivalence::Equiv,
    gen_inputs: fn() -> Vec<Value>,
) {
    r.push(CorpusEntry {
        name,
        category,
        phase,
        ordering,
        primitives,
        compose,
        oracle,
        equiv,
        gen_inputs,
    });
}
