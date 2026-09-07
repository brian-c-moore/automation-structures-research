// Classical algorithm instantiations.
//
// 87 algorithms from the algorithm corpus, vendored from supplementary-research/studies/domain-corpora/algorithms/rust/src/
// compositions/phase*.rs with Verus annotations. Each algorithm is a
// composition of primitives (Reduction, ResourceRegistry,
// TraversalEngine, ActuationPass, Bisection, Sampler) through a
// composition pattern (Memoization, sort_then_scan,
// priority_driven_propagation, sliding_window, monotonic_stack,
// monotonic_deque). The per-algorithm content is the cell-fill /
// state-transition specific to the algorithm; the outer loop shape
// is shared with all algorithms in the same phase.
//
// Each algorithm carries a written Verus specification plus a KAT
// cross-check against the executable Rust oracle in
// supplementary-research/studies/domain-corpora/algorithms/rust/.

pub mod phase1_dp;
pub mod phase2_stack_bsearch;
pub mod phase3_adv_graphs;
pub mod phase4_backtracking;
pub mod phase5_trees_heap;
pub mod phase6_arrays;
pub mod phase7_lists_tries_graphs;
pub mod phase8_greedy_intervals_math_bit;
