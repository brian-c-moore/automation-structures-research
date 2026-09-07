// Classical algorithm composition patterns.
//
// Composition patterns from the algorithm corpus. The TLA+ side has
// TLC-PASS specs for Memoization, MonotonicStack, and MonotonicDeque at
// supplementary-research/studies/domain-corpora/algorithms/tla/compositions/
// but no TLAPS `_Proof.tla` files, so the Verus verification here is
// the implementation-conformance evidence in the absence of a
// structural TLAPS lift.
//
// The patterns verified in this module tree:
//
// memoization                  — DAG-fill memoization (mirrors TLA+ MemoizationComposition.tla)
// sort_then_scan               — Sort then linear scan (intervals, greedy)
// priority_driven_propagation  — Min-extraction primitive (Dijkstra, Prim, A*)
// sliding_window               — Linear scan with moving window
// monotonic_stack              — Stack with monotonic invariant (next-greater-element)
// monotonic_deque              — Deque with monotonic invariant (sliding-window-max)
//
// Individual algorithm instantiations exercise additional pattern shapes
// (two-pointer, hash table, tree recursion, backtracking, greedy,
// trie); those receive evidence via the KAT-cross-check layer
// in supplementary-research/studies/domain-corpora/algorithms/verus/.

pub mod memoization;
pub mod monotonic_deque;
pub mod monotonic_stack;
pub mod priority_driven_propagation;
pub mod sliding_window;
pub mod sort_then_scan;
