//! Phase 5 — Trees and Heap / Priority Queue.
//!
//! ## Tree encoding (identical in Rust and Python)
//!
//! The tree is represented as a **level-order array**. Index 0 is the
//! root; the children of the node at index `i` are at indices
//! `2*i + 1` (left) and `2*i + 2` (right). A missing node is the
//! sentinel `Value::Int(NULL_NODE)` (`-100_000`). Input values stay in
//! the range `[-9999, 9999]`, well away from the sentinel.
//!
//! `children` / `is_live` translate between the array form and the
//! index-based traversal model. Only occupied (non-sentinel) indices are
//! considered live nodes.
//!
//! ## Composition shape
//!
//! - Tree algorithms: **TraversalEngine** (dfs/bfs) + **Reduction**
//!   (per-node aggregate), housed in a **ResourceRegistry** when a
//!   memo table is needed.
//! - Heap algorithms: **PriorityQueue** / **CompetitiveSelection**
//!   (hard for extract-extremum, ranked for top-K).  Min-heap behaviour
//!   is obtained by negating values before insertion into the max-heap
//!   `PriorityQueue<i64>` (the standard sign-flip trick; no wrapper
//!   type is needed, keeping the primitive interface clean).
//! - No `std::collections::BinaryHeap` called directly in algorithm
//!   code; no recursion bypassing the primitives.
//!
//! ## Heap encoding constraint
//!
//! `PriorityQueue<T>` derives `PartialEq`, which does not compile for
//! `T = std::cmp::Reverse<i64>` because `BinaryHeap<T>` does not
//! implement `PartialEq`. All heap algorithms therefore use
//! `PriorityQueue<i64>` with the sign-flip encoding for min-heap
//! behaviour.

use super::{entry, gen};
use crate::config::CorpusEntry;
use crate::equivalence::Equiv;
use crate::primitives::{
    ActuationPass, CompetitiveSelection, PriorityQueue, Reduction, ResourceRegistry,
    TraversalEngine,
};
use crate::value::Value;

// -----------------------------------------------------------------------
// Tree encoding constants and helpers
// -----------------------------------------------------------------------

/// Sentinel value for a null / absent child in the level-order encoding.
const NULL_NODE: i64 = -100_000;

/// True iff index `i` is a live (non-sentinel) node.
fn is_live(arr: &[i64], i: usize) -> bool {
    i < arr.len() && arr[i] != NULL_NODE
}

/// Live children of node at index `i`.
fn children(arr: &[i64], i: usize) -> Vec<usize> {
    let mut kids = Vec::new();
    let l = 2 * i + 1;
    let r = 2 * i + 2;
    if is_live(arr, l) {
        kids.push(l);
    }
    if is_live(arr, r) {
        kids.push(r);
    }
    kids
}

/// Decode a `Value::List` of `Value::Int` to `Vec<i64>`.
fn tree_vals(v: &Value) -> Vec<i64> {
    v.as_list().iter().map(|x| x.as_int()).collect()
}

/// Iterative in-order traversal using an explicit stack (a substrate buffer —
/// a plain `Vec`, not a registry). Each index is visited once.
fn inorder(arr: &[i64]) -> Vec<usize> {
    let mut result = Vec::new();
    let mut stack: Vec<usize> = Vec::new();
    let mut cur: Option<usize> = if is_live(arr, 0) { Some(0) } else { None };
    loop {
        // Descend left as far as possible.
        while let Some(c) = cur {
            stack.push(c);
            let l = 2 * c + 1;
            cur = if is_live(arr, l) { Some(l) } else { None };
        }
        match stack.pop() {
            None => break,
            Some(n) => {
                result.push(n);
                let rc = 2 * n + 2;
                cur = if is_live(arr, rc) { Some(rc) } else { None };
            }
        }
    }
    result
}

// -----------------------------------------------------------------------
// Invert Binary Tree
// BFS traversal with interleaved ActuationPass (swap children) and
// post-swap child expansion.  The BFS frontier uses a VecDeque (substrate
// buffer).  The visited set (a ResourceRegistry) is not load-bearing here:
// a tree has no shared structure, so BFS cannot revisit a node.  The
// registered composition omits it.  Swap and
// expansion are interleaved because the children enqueued after each swap are
// determined by the post-swap liveness of the child slots.
//
// Ordering: Tree
// -----------------------------------------------------------------------
fn invert_binary_tree(input: Value) -> Value {
    let mut arr = tree_vals(&input);
    if arr.is_empty() || !is_live(&arr, 0) {
        return Value::List(arr.iter().map(|&x| Value::Int(x)).collect());
    }
    use std::collections::VecDeque;
    // ResourceRegistry as visited set (TraversalEngine invariant).
    let mut visited: ResourceRegistry<usize, ()> = ResourceRegistry::new();
    let mut queue: VecDeque<usize> = VecDeque::new();
    visited.insert(0, ());
    queue.push_back(0);
    while let Some(i) = queue.pop_front() {
        let l = 2 * i + 1;
        let r = 2 * i + 2;
        // ActuationPass: swap the two child slots in place.
        while arr.len() <= r.max(l) {
            arr.push(NULL_NODE);
        }
        arr.swap(l, r);
        // Enqueue live children AFTER the swap (post-swap liveness).
        for c in [l, r] {
            if is_live(&arr, c) && !visited.contains(&c) {
                visited.insert(c, ());
                queue.push_back(c);
            }
        }
    }
    // Trim trailing sentinels for canonical output.
    while arr.last() == Some(&NULL_NODE) {
        arr.pop();
    }
    Value::List(arr.iter().map(|&x| Value::Int(x)).collect())
}

// -----------------------------------------------------------------------
// Maximum Depth of Binary Tree
// TraversalEngine (BFS) to visit all nodes; Reduction(max) bottom-up.
// Process nodes in reverse BFS order (leaves before parents, post-order
// approximation).  The depth table (a ResourceRegistry) is specific to this
// iterative reverse-BFS form: a recursive post-order returns the depth
// directly and needs no table.  The registered composition omits it.
// Ordering: Tree
// -----------------------------------------------------------------------
fn max_depth(input: Value) -> Value {
    let arr = tree_vals(&input);
    if arr.is_empty() || !is_live(&arr, 0) {
        return Value::Int(0);
    }
    let arr_snap = arr.clone();
    let bfs_order = TraversalEngine::bfs(0usize, |&i| children(&arr_snap, i));
    let mut depth: ResourceRegistry<usize, i64> = ResourceRegistry::new();
    // Reverse BFS = process leaves first (post-order-like).
    for &i in bfs_order.iter().rev() {
        let child_depths: Vec<i64> = children(&arr_snap, i)
            .into_iter()
            .map(|c| *depth.lookup(&c).unwrap_or(&0))
            .collect();
        let d = 1 + Reduction::reduce(child_depths, 0i64, |a, b| a.max(b));
        depth.insert(i, d);
    }
    Value::Int(*depth.lookup(&0).unwrap_or(&0))
}

// -----------------------------------------------------------------------
// Same Tree
// Synchronized dual TraversalEngine (index-space BFS) + Reduction(AND).
// Input: [treeA_list, treeB_list]
// Output: Bool
// Ordering: Tree
// -----------------------------------------------------------------------
fn same_tree(input: Value) -> Value {
    let parts = input.as_list();
    let a = tree_vals(&parts[0]);
    let b = tree_vals(&parts[1]);
    let max_idx = a.len().max(b.len());
    if max_idx == 0 {
        return Value::Bool(true);
    }
    // BFS over the combined index space: expand child slots for any index
    // that is live in either tree.
    let a2 = a.clone();
    let b2 = b.clone();
    let order = TraversalEngine::bfs(0usize, move |&i| {
        let live_a = i < a2.len() && a2[i] != NULL_NODE;
        let live_b = i < b2.len() && b2[i] != NULL_NODE;
        if !(live_a || live_b) {
            return vec![];
        }
        let l = 2 * i + 1;
        let r = 2 * i + 2;
        let mut kids = Vec::new();
        // Expand if the child position could exist in either tree.
        if l < max_idx * 2 + 3 {
            kids.push(l);
        }
        if r < max_idx * 2 + 3 {
            kids.push(r);
        }
        kids
    });
    // Reduction: AND over per-index equality predicate.
    let results: Vec<bool> = order
        .into_iter()
        .map(|i| {
            let va = if i < a.len() { a[i] } else { NULL_NODE };
            let vb = if i < b.len() { b[i] } else { NULL_NODE };
            va == vb
        })
        .collect();
    Value::Bool(Reduction::reduce(results, true, |acc, x| acc && x))
}

// -----------------------------------------------------------------------
// Binary Tree Level Order Traversal
// TraversalEngine (BFS) with manual level-boundary counting.
// Output: List of lists (one per level) — Equiv::Exact
// Ordering: Tree
// -----------------------------------------------------------------------
fn level_order(input: Value) -> Value {
    let arr = tree_vals(&input);
    if arr.is_empty() || !is_live(&arr, 0) {
        return Value::List(vec![]);
    }
    // BFS with explicit level batching (queue-size trick).
    use std::collections::VecDeque;
    let mut queue: VecDeque<usize> = VecDeque::new();
    queue.push_back(0);
    let mut levels: Vec<Value> = Vec::new();
    while !queue.is_empty() {
        let level_size = queue.len();
        let mut level_vals = Vec::new();
        for _ in 0..level_size {
            let i = queue.pop_front().unwrap();
            level_vals.push(Value::Int(arr[i]));
            for c in children(&arr, i) {
                queue.push_back(c);
            }
        }
        levels.push(Value::List(level_vals));
    }
    Value::List(levels)
}

// -----------------------------------------------------------------------
// Validate Binary Search Tree
// In-order traversal (iterative) + Reduction over the sequence
// (last-seen value tracking, strict-increase predicate).
// Output: Bool
// Ordering: Linear (in-order sequence is a chain)
// -----------------------------------------------------------------------
fn validate_bst(input: Value) -> Value {
    let arr = tree_vals(&input);
    if arr.is_empty() || !is_live(&arr, 0) {
        return Value::Bool(true);
    }
    let order = inorder(&arr);
    // Reduction: fold over (last_value, valid) state.
    let (_, valid) = order.into_iter().fold((i64::MIN, true), |(prev, ok), i| {
        if !ok {
            return (prev, false);
        }
        let v = arr[i];
        if v <= prev {
            (v, false)
        } else {
            (v, true)
        }
    });
    Value::Bool(valid)
}

// -----------------------------------------------------------------------
// Binary Tree Maximum Path Sum
// Post-order TraversalEngine (reverse BFS) + Reduction at two levels:
//   per-node: max single-direction gain (propagated to parent)
//   global:   max through-node path sum updated via Reduction(max)
// The gain table (a ResourceRegistry) is specific to this iterative
// reverse-BFS form: a recursive post-order's return value carries the gain,
// so no table is needed.  The registered composition omits it.
// Ordering: Tree
// -----------------------------------------------------------------------
fn max_path_sum(input: Value) -> Value {
    let arr = tree_vals(&input);
    if arr.is_empty() || !is_live(&arr, 0) {
        return Value::Int(0);
    }
    let arr_snap = arr.clone();
    let bfs_order = TraversalEngine::bfs(0usize, |&i| children(&arr_snap, i));
    let mut gain: ResourceRegistry<usize, i64> = ResourceRegistry::new();
    let mut global_max = i64::MIN;
    for &i in bfs_order.iter().rev() {
        let v = arr_snap[i];
        let l = 2 * i + 1;
        let r = 2 * i + 2;
        let lg = if is_live(&arr_snap, l) {
            *gain.lookup(&l).unwrap_or(&0)
        } else {
            0
        };
        let rg = if is_live(&arr_snap, r) {
            *gain.lookup(&r).unwrap_or(&0)
        } else {
            0
        };
        // Single-direction gain from this node (max of either child + self, at least 0).
        let best_child = Reduction::reduce(vec![lg, rg, 0i64], i64::MIN, |a, b| a.max(b));
        gain.insert(i, v + best_child);
        // Through-node sum: both children contribute (each clamped to 0).
        let through = v
            + Reduction::reduce(vec![lg, 0i64], i64::MIN, |a, b| a.max(b))
            + Reduction::reduce(vec![rg, 0i64], i64::MIN, |a, b| a.max(b));
        global_max = Reduction::reduce(vec![global_max, through], i64::MIN, |a, b| a.max(b));
    }
    Value::Int(global_max)
}

// -----------------------------------------------------------------------
// Kth Largest Element in a Stream
// PriorityQueue<i64> used as a min-heap via sign-flip: push -x, the
// maximum of -x values equals the minimum of x values.
// CompetitiveSelection-ranked: maintain a size-K set whose minimum = Kth
// largest.
// Input: [k, [[kind, val], ...]]
//   kind=0 → add val (no output)
//   kind=1 → add val then query (Kth largest)
// Output: Value::List of query results
// Ordering: Linear
// -----------------------------------------------------------------------
fn kth_largest_stream(input: Value) -> Value {
    let parts = input.as_list();
    let k = parts[0].as_int() as usize;
    let ops = parts[1].as_list();
    // Min-heap of size K via sign-flip: PriorityQueue stores -val so
    // pop_best() returns the most-negative, i.e., the minimum original value.
    let mut pq: PriorityQueue<i64> = PriorityQueue::new();
    let mut results: Vec<Value> = Vec::new();
    for op in ops {
        let o = op.as_list();
        let kind = o[0].as_int();
        let x = o[1].as_int();
        pq.push(-x); // sign-flip: max-heap over -x = min-heap over x
                     // Evict largest -x (= smallest x) to maintain size K.
        while pq.len() > k {
            pq.pop_best();
        }
        if kind == 1 {
            // Kth largest = minimum of the K largest = -peek (sign-flip back).
            let ans = pq.peek().map(|&neg| -neg).unwrap_or(i64::MIN);
            results.push(Value::Int(ans));
        }
    }
    Value::List(results)
}

// -----------------------------------------------------------------------
// Last Stone Weight
// PriorityQueue<i64> (max-heap) + ActuationPass (the smash-combine step).
// Input: List[Int] — stone weights (≥ 1)
// Output: Int (remaining weight, or 0 if none left)
// Ordering: Linear
// -----------------------------------------------------------------------
fn last_stone_weight(input: Value) -> Value {
    let stones = input.as_int_vec();
    let mut pq: PriorityQueue<i64> = PriorityQueue::new();
    ActuationPass::apply_each(stones, |s| pq.push(s));
    while pq.len() >= 2 {
        // CompetitiveSelection::hard = extract the two maximums.
        let a = pq.pop_best().unwrap(); // heaviest
        let b = pq.pop_best().unwrap(); // second heaviest
        let diff = a - b; // a >= b by max-heap property
        if diff > 0 {
            pq.push(diff);
        }
        // If diff == 0 both stones destroyed; nothing pushed back.
    }
    Value::Int(pq.pop_best().unwrap_or(0))
}

// -----------------------------------------------------------------------
// K Closest Points to Origin
// CompetitiveSelection::ranked by score = -dist² (descending rank =
// ascending distance).
// Input: [[[x,y], ...], k]
// Output: List of k points — Equiv::SetOfIntLists
// Ordering: Tree (distance computations independent per point)
// -----------------------------------------------------------------------
fn k_closest_points(input: Value) -> Value {
    let parts = input.as_list();
    let points: Vec<Vec<i64>> = parts[0].as_list().iter().map(|p| p.as_int_vec()).collect();
    let k = parts[1].as_int() as usize;
    if k == 0 || points.is_empty() {
        return Value::List(vec![]);
    }
    // Score: -dist² so that the k highest scores are the k closest points.
    let top_k = CompetitiveSelection::ranked(&points, k, |p| -(p[0] * p[0] + p[1] * p[1]));
    Value::List(top_k.into_iter().map(|p| Value::ints(&p)).collect())
}

// -----------------------------------------------------------------------
// Find Median from Data Stream
// Two PriorityQueue<i64> structures under a balance invariant:
//   lo: max-heap holding the lower half (stores x directly)
//   hi: min-heap holding the upper half (stores -x via sign-flip)
// ActuationPass drives the rebalance step.
// Input: [[kind, val], ...]  kind=0 → add, kind=1 → query
// Output: List of (median × 2) as Int (avoids fractions; Python matches).
// Ordering: Linear
// -----------------------------------------------------------------------
fn find_median_stream(input: Value) -> Value {
    let ops = input.as_list();
    // lo: max-heap (lower half); hi: max-heap over -x (upper half, min-heap).
    let mut lo: PriorityQueue<i64> = PriorityQueue::new(); // stores x, max at top
    let mut hi: PriorityQueue<i64> = PriorityQueue::new(); // stores -x, min of x at top
    let mut results: Vec<Value> = Vec::new();
    for op in ops {
        let o = op.as_list();
        let kind = o[0].as_int();
        if kind == 0 {
            let x = o[1].as_int();
            let lo_max = lo.peek().copied().unwrap_or(i64::MIN);
            if x <= lo_max {
                lo.push(x);
            } else {
                hi.push(-x); // sign-flip: min-heap over x
            }
            // ActuationPass: rebalance so sizes differ by at most 1.
            if lo.len() > hi.len() + 1 {
                let v = lo.pop_best().unwrap();
                hi.push(-v);
            } else if hi.len() > lo.len() {
                let neg_v = hi.pop_best().unwrap();
                lo.push(-neg_v); // sign-flip back
            }
        } else {
            // Query: median × 2.
            let median_x2 = if lo.len() == hi.len() {
                let lo_top = lo.peek().copied().unwrap_or(0);
                let hi_top = hi.peek().map(|&neg| -neg).unwrap_or(0);
                lo_top + hi_top
            } else {
                // lo has one more element.
                lo.peek().copied().unwrap_or(0) * 2
            };
            results.push(Value::Int(median_x2));
        }
    }
    Value::List(results)
}

// -----------------------------------------------------------------------
// Input generators
// -----------------------------------------------------------------------

/// `count` random level-order trees, each up to `max_nodes` live nodes,
/// values in `[lo, hi]` (must avoid NULL_NODE = -100_000).
fn rand_tree(seed: u64, count: usize, max_nodes: usize, lo: i64, hi: i64) -> Vec<Value> {
    use crate::primitives::Sampler;
    let mut s = Sampler::new(seed);
    let span = (hi - lo + 1).max(1) as usize;
    (0..count)
        .map(|_| {
            let n = 1 + s.pick_index(max_nodes);
            let arr: Vec<Value> = (0..n)
                .map(|_| Value::Int(lo + s.pick_index(span) as i64))
                .collect();
            Value::List(arr)
        })
        .collect()
}

/// Small collection of hand-curated trees exercising edge cases.
fn curated_trees() -> Vec<Value> {
    vec![
        // Empty tree
        Value::List(vec![]),
        // Single node
        Value::List(vec![Value::Int(1)]),
        // Full binary tree
        Value::List(vec![
            Value::Int(4),
            Value::Int(2),
            Value::Int(7),
            Value::Int(1),
            Value::Int(3),
            Value::Int(6),
            Value::Int(9),
        ]),
        // Right-spine only: root=1, right=2, right-right=3
        Value::List(vec![
            Value::Int(1),
            Value::Int(NULL_NODE),
            Value::Int(2),
            Value::Int(NULL_NODE),
            Value::Int(NULL_NODE),
            Value::Int(NULL_NODE),
            Value::Int(3),
        ]),
        // Left-leaning: root=1, left=2, left-left=3
        Value::List(vec![
            Value::Int(1),
            Value::Int(2),
            Value::Int(NULL_NODE),
            Value::Int(3),
        ]),
    ]
}

fn g_invert() -> Vec<Value> {
    let mut v = curated_trees();
    v.extend(rand_tree(51, 1000, 15, -99, 99));
    v
}

fn g_max_depth() -> Vec<Value> {
    let mut v = curated_trees();
    v.extend(rand_tree(52, 1000, 15, 1, 99));
    v
}

fn g_same_tree() -> Vec<Value> {
    let mut v = vec![
        Value::List(vec![Value::List(vec![]), Value::List(vec![])]),
        Value::List(vec![
            Value::List(vec![Value::Int(1)]),
            Value::List(vec![Value::Int(1)]),
        ]),
        Value::List(vec![
            Value::List(vec![Value::Int(1)]),
            Value::List(vec![Value::Int(2)]),
        ]),
        Value::List(vec![
            Value::List(vec![Value::Int(1), Value::Int(2), Value::Int(3)]),
            Value::List(vec![Value::Int(1), Value::Int(2), Value::Int(3)]),
        ]),
        Value::List(vec![
            Value::List(vec![Value::Int(1), Value::Int(2)]),
            Value::List(vec![Value::Int(1), Value::Int(NULL_NODE), Value::Int(2)]),
        ]),
    ];
    let trees_a = rand_tree(53, 500, 7, 1, 9);
    let trees_b = rand_tree(54, 500, 7, 1, 9);
    for (a, b) in trees_a.into_iter().zip(trees_b) {
        v.push(Value::List(vec![a, b]));
    }
    v
}

fn g_level_order() -> Vec<Value> {
    let mut v = curated_trees();
    v.extend(rand_tree(55, 1000, 15, 1, 99));
    v
}

/// Random valid BST trees built by insertion.
fn rand_bst(seed: u64, count: usize, max_nodes: usize) -> Vec<Value> {
    use crate::primitives::Sampler;
    let mut s = Sampler::new(seed);
    (0..count)
        .map(|_| {
            let n = 1 + s.pick_index(max_nodes);
            let mut arr: Vec<i64> = vec![NULL_NODE; 3];
            let first = 1 + s.pick_index(198) as i64;
            arr[0] = first;
            for _ in 1..n {
                let val = 1 + s.pick_index(198) as i64;
                let mut idx = 0usize;
                loop {
                    if arr[idx] == NULL_NODE {
                        arr[idx] = val;
                        break;
                    }
                    // Skip equal values (BST requires strict ordering)
                    if val == arr[idx] {
                        break;
                    }
                    let next = if val < arr[idx] {
                        2 * idx + 1
                    } else {
                        2 * idx + 2
                    };
                    if next >= arr.len() {
                        arr.resize(next + 2, NULL_NODE);
                    }
                    idx = next;
                }
            }
            while arr.last() == Some(&NULL_NODE) {
                arr.pop();
            }
            Value::List(arr.iter().map(|&x| Value::Int(x)).collect())
        })
        .collect()
}

/// Random invalid BST trees: take a valid BST and swap two live values.
fn rand_invalid_bst(seed: u64, count: usize, max_nodes: usize) -> Vec<Value> {
    use crate::primitives::Sampler;
    let mut s = Sampler::new(seed);
    rand_bst(seed + 1000, count, max_nodes)
        .into_iter()
        .map(|tree| {
            let mut arr = tree_vals(&tree);
            let live: Vec<usize> = (0..arr.len()).filter(|&i| arr[i] != NULL_NODE).collect();
            if live.len() < 2 {
                return Value::List(arr.iter().map(|&x| Value::Int(x)).collect());
            }
            let i = live[s.pick_index(live.len())];
            let j = live[s.pick_index(live.len())];
            if i != j && arr[i] != arr[j] {
                arr.swap(i, j);
            }
            Value::List(arr.iter().map(|&x| Value::Int(x)).collect())
        })
        .collect()
}

fn g_validate_bst() -> Vec<Value> {
    let mut v = vec![
        Value::List(vec![]),
        Value::List(vec![Value::Int(5), Value::Int(3), Value::Int(7)]),
        Value::List(vec![Value::Int(5), Value::Int(3), Value::Int(4)]),
        Value::List(vec![Value::Int(2), Value::Int(1), Value::Int(3)]),
        // Invalid: node 6 (at index 5, right child of root) < root (5 at root's right):
        // [5, 4, 6, null, null, 3, 7] — 3 is in right subtree of 5, violates BST.
        Value::List(vec![
            Value::Int(5),
            Value::Int(4),
            Value::Int(6),
            Value::Int(NULL_NODE),
            Value::Int(NULL_NODE),
            Value::Int(3),
            Value::Int(7),
        ]),
    ];
    v.extend(rand_bst(56, 500, 10));
    v.extend(rand_invalid_bst(57, 500, 10));
    v
}

fn g_max_path_sum() -> Vec<Value> {
    let mut v = vec![
        Value::List(vec![Value::Int(1), Value::Int(2), Value::Int(3)]),
        Value::List(vec![Value::Int(-3), Value::Int(-2), Value::Int(-1)]),
        Value::List(vec![Value::Int(5)]),
        Value::List(vec![Value::Int(1), Value::Int(-2), Value::Int(3)]),
        // Classic LeetCode example: [-10, 9, 20, null, null, 15, 7] → 42
        Value::List(vec![
            Value::Int(-10),
            Value::Int(9),
            Value::Int(20),
            Value::Int(NULL_NODE),
            Value::Int(NULL_NODE),
            Value::Int(15),
            Value::Int(7),
        ]),
    ];
    v.extend(rand_tree(58, 1000, 15, -50, 50));
    v
}

fn g_kth_largest() -> Vec<Value> {
    use crate::primitives::Sampler;
    let mut s = Sampler::new(59);
    let mut v = vec![
        // k=3, add 4,5,8; query after adding 2 → 4; query after adding 3 → 4
        Value::List(vec![
            Value::Int(3),
            Value::List(vec![
                Value::List(vec![Value::Int(0), Value::Int(4)]),
                Value::List(vec![Value::Int(0), Value::Int(5)]),
                Value::List(vec![Value::Int(0), Value::Int(8)]),
                Value::List(vec![Value::Int(1), Value::Int(2)]),
                Value::List(vec![Value::Int(1), Value::Int(3)]),
            ]),
        ]),
    ];
    for _ in 0..1000 {
        let k = 1 + s.pick_index(4) as i64;
        let n_ops = 2 + s.pick_index(28);
        let mut ops = Vec::new();
        let mut added = 0usize;
        for j in 0..n_ops {
            let val = (s.pick_index(50) as i64) - 10;
            // Ensure first k ops are adds so the heap has k elements before any query.
            let kind = if added < k as usize || j % 3 != 2 {
                0i64
            } else {
                1
            };
            if kind == 0 {
                added += 1;
            }
            ops.push(Value::List(vec![Value::Int(kind), Value::Int(val)]));
        }
        v.push(Value::List(vec![Value::Int(k), Value::List(ops)]));
    }
    v
}

fn g_last_stone() -> Vec<Value> {
    let mut v = vec![
        Value::List(vec![
            Value::Int(2),
            Value::Int(7),
            Value::Int(4),
            Value::Int(1),
            Value::Int(8),
            Value::Int(1),
        ]),
        Value::List(vec![Value::Int(1)]),
        Value::List(vec![]),
        Value::List(vec![Value::Int(3), Value::Int(3)]),
    ];
    v.extend(gen::rand_int_lists(60, 1000, 20, 1, 30));
    v
}

fn g_k_closest() -> Vec<Value> {
    use crate::primitives::Sampler;
    let mut s = Sampler::new(61);
    let mut v = vec![
        Value::List(vec![
            Value::List(vec![
                Value::List(vec![Value::Int(1), Value::Int(3)]),
                Value::List(vec![Value::Int(-2), Value::Int(2)]),
            ]),
            Value::Int(1),
        ]),
        Value::List(vec![
            Value::List(vec![
                Value::List(vec![Value::Int(3), Value::Int(3)]),
                Value::List(vec![Value::Int(5), Value::Int(-1)]),
                Value::List(vec![Value::Int(-2), Value::Int(4)]),
            ]),
            Value::Int(2),
        ]),
    ];
    for _ in 0..1000 {
        let n = 1 + s.pick_index(15);
        let k = 1 + s.pick_index(n);
        let pts: Vec<Value> = (0..n)
            .map(|_| {
                let x = (s.pick_index(21) as i64) - 10;
                let y = (s.pick_index(21) as i64) - 10;
                Value::List(vec![Value::Int(x), Value::Int(y)])
            })
            .collect();
        v.push(Value::List(vec![Value::List(pts), Value::Int(k as i64)]));
    }
    v
}

fn g_find_median() -> Vec<Value> {
    use crate::primitives::Sampler;
    let mut s = Sampler::new(62);
    let mut v = vec![
        // add 1, add 2, query (1+2=3), add 3, query (2*2=4)
        Value::List(vec![
            Value::List(vec![Value::Int(0), Value::Int(1)]),
            Value::List(vec![Value::Int(0), Value::Int(2)]),
            Value::List(vec![Value::Int(1), Value::Int(0)]),
            Value::List(vec![Value::Int(0), Value::Int(3)]),
            Value::List(vec![Value::Int(1), Value::Int(0)]),
        ]),
    ];
    for _ in 0..1000 {
        let n_ops = 2 + s.pick_index(28);
        let mut ops = Vec::new();
        let mut added = 0usize;
        for j in 0..n_ops {
            let val = (s.pick_index(40) as i64) - 10;
            let kind = if added == 0 || j % 4 != 3 { 0i64 } else { 1 };
            if kind == 0 {
                added += 1;
            }
            ops.push(Value::List(vec![Value::Int(kind), Value::Int(val)]));
        }
        v.push(Value::List(ops));
    }
    v
}

// -----------------------------------------------------------------------
// Registration
// -----------------------------------------------------------------------
pub fn add(r: &mut Vec<CorpusEntry>) {
    let te_act = "TraversalEngine + ActuationPass";
    let te_r = "TraversalEngine + Reduction";
    let lo_lbl = "TraversalEngine(BFS, level-batched) + queue frontier (substrate buffer)";
    let vbst = "TraversalEngine(in-order) + Reduction";
    let pq_ranked = "PriorityQueue(CompetitiveSelection-ranked)";
    let pq_hard = "PriorityQueue(CompetitiveSelection-hard) + ActuationPass";
    let cs_ranked = "CompetitiveSelection-ranked";
    let pq_hard2 = "PriorityQueue x2 (CompetitiveSelection-hard) + ActuationPass";

    entry(
        r,
        "Invert Binary Tree",
        "Trees",
        5,
        "Tree",
        te_act,
        invert_binary_tree,
        "invert_binary_tree",
        Equiv::Exact,
        g_invert,
    );
    entry(
        r,
        "Maximum Depth of Binary Tree",
        "Trees",
        5,
        "Tree",
        te_r,
        max_depth,
        "max_depth",
        Equiv::Exact,
        g_max_depth,
    );
    entry(
        r,
        "Same Tree",
        "Trees",
        5,
        "Tree",
        te_r,
        same_tree,
        "same_tree",
        Equiv::BoolEq,
        g_same_tree,
    );
    entry(
        r,
        "Binary Tree Level Order Traversal",
        "Trees",
        5,
        "Tree",
        lo_lbl,
        level_order,
        "level_order",
        Equiv::Exact,
        g_level_order,
    );
    entry(
        r,
        "Validate Binary Search Tree",
        "Trees",
        5,
        "Linear",
        vbst,
        validate_bst,
        "validate_bst",
        Equiv::BoolEq,
        g_validate_bst,
    );
    entry(
        r,
        "Binary Tree Maximum Path Sum",
        "Trees",
        5,
        "Tree",
        te_r,
        max_path_sum,
        "max_path_sum",
        Equiv::Exact,
        g_max_path_sum,
    );
    entry(
        r,
        "Kth Largest in Stream",
        "Heap",
        5,
        "Linear",
        pq_ranked,
        kth_largest_stream,
        "kth_largest_stream",
        Equiv::Exact,
        g_kth_largest,
    );
    entry(
        r,
        "Last Stone Weight",
        "Heap",
        5,
        "Linear",
        pq_hard,
        last_stone_weight,
        "last_stone_weight",
        Equiv::Exact,
        g_last_stone,
    );
    entry(
        r,
        "K Closest Points to Origin",
        "Heap",
        5,
        "Tree",
        cs_ranked,
        k_closest_points,
        "k_closest_points",
        Equiv::SetOfIntLists,
        g_k_closest,
    );
    entry(
        r,
        "Find Median from Data Stream",
        "Heap",
        5,
        "Linear",
        pq_hard2,
        find_median_stream,
        "find_median_stream",
        Equiv::Exact,
        g_find_median,
    );
}
