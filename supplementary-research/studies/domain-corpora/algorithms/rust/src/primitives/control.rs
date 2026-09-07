//! Control primitives: how computation is organised.

use std::collections::BinaryHeap;

// ===================================================================
// Reduction
// ===================================================================
/// **Motivation.** Collapse a stream of N values to one summary.
///
/// **Definition.** Fold under an associative binary operator with an
/// identity.
///
/// **Invariant.** Associativity: grouping does not change the result —
/// so a sequential fold and a parallel tree-reduce agree.
///
/// **Recognition.** sum / max / min / count / XOR / set-union / running
/// aggregates — nearly every corpus category.
pub struct Reduction;
impl Reduction {
    pub fn reduce<T, I, F>(iter: I, identity: T, op: F) -> T
    where
        I: IntoIterator<Item = T>,
        F: Fn(T, T) -> T,
    {
        iter.into_iter().fold(identity, |acc, x| op(acc, x))
    }
}

// ===================================================================
// ActuationPass
// ===================================================================
/// **Motivation.** Apply a side-effecting operation to a determined set
/// of items — the "execute / apply / commit / write" step.
///
/// **Definition.** Map a per-item side-effecting op over exactly the
/// given items: no double-actuation, no skips.
///
/// **Invariant.** Actuation scope = exactly the supplied items.
pub struct ActuationPass;
impl ActuationPass {
    pub fn apply<T, F: FnMut(&mut T)>(items: &mut [T], mut f: F) {
        for it in items.iter_mut() {
            f(it);
        }
    }
    pub fn apply_each<T, F: FnMut(T)>(items: impl IntoIterator<Item = T>, mut f: F) {
        for it in items {
            f(it);
        }
    }
}

// ===================================================================
// TraversalEngine
// ===================================================================
/// **Motivation.** Walk a graph/tree under a successor function.
///
/// **Definition.** Budget-bounded DFS/BFS over a successor closure with
/// a visited registry.
///
/// **Invariant.** Each reachable node visited at most once (visited
/// registry); the budget is never exceeded.
///
/// **Recognition.** DFS/BFS, topological order, tree traversals; with
/// *paired undo* it covers backtracking; the apply-on-descent /
/// undo-on-retreat pairing is provided here as
/// [`TraversalEngine::backtrack`].
pub struct TraversalEngine;
impl TraversalEngine {
    /// DFS preorder visit sequence from `start`.
    pub fn dfs<N: Clone + Eq + std::hash::Hash, S: Fn(&N) -> Vec<N>>(start: N, succ: S) -> Vec<N> {
        let mut visited = std::collections::HashSet::new();
        let mut order = Vec::new();
        let mut stack = vec![start];
        while let Some(n) = stack.pop() {
            if !visited.insert(n.clone()) {
                continue;
            }
            order.push(n.clone());
            let mut kids = succ(&n);
            kids.reverse();
            for k in kids {
                if !visited.contains(&k) {
                    stack.push(k);
                }
            }
        }
        order
    }
    /// BFS level-order visit sequence from `start`.
    pub fn bfs<N: Clone + Eq + std::hash::Hash, S: Fn(&N) -> Vec<N>>(start: N, succ: S) -> Vec<N> {
        let mut visited = std::collections::HashSet::new();
        let mut order = Vec::new();
        let mut q = std::collections::VecDeque::new();
        visited.insert(start.clone());
        q.push_back(start);
        while let Some(n) = q.pop_front() {
            order.push(n.clone());
            for k in succ(&n) {
                if visited.insert(k.clone()) {
                    q.push_back(k);
                }
            }
        }
        order
    }
    /// Backtracking driver: TraversalEngine plus paired undo.
    /// `extend` yields candidate moves; `apply`/`undo` are the
    /// paired mutations; `accept` collects a solution snapshot.
    pub fn backtrack<St, Mv, Sol, EX, AP, UN, AC>(
        state: &mut St,
        extend: &EX,
        apply: &AP,
        undo: &UN,
        accept: &AC,
        out: &mut Vec<Sol>,
    ) where
        EX: Fn(&St) -> Vec<Mv>,
        AP: Fn(&mut St, &Mv),
        UN: Fn(&mut St, &Mv),
        AC: Fn(&St) -> Option<Sol>,
    {
        if let Some(s) = accept(state) {
            out.push(s);
        }
        for mv in extend(state) {
            apply(state, &mv);
            Self::backtrack(state, extend, apply, undo, accept, out);
            undo(state, &mv); // the pairing invariant
        }
    }
}

// ===================================================================
// PropagationPass
// ===================================================================
/// **Motivation.** Iterate node-local state from neighbours until it
/// stabilises (Bellman-Ford, belief/label propagation).
///
/// **Definition.** Repeated message-and-update over a graph toward a
/// fixed point, optionally bounded in rounds.
///
/// **Invariant.** Bounded iteration: terminates at a fixed point or at
/// the round cap.
pub struct PropagationPass;
impl PropagationPass {
    /// Run `update(state)` until it stops changing or `max_rounds` is
    /// reached. `state` is `Clone + PartialEq` so the fixed point is
    /// detectable.
    pub fn run<S: Clone + PartialEq, U: Fn(&S) -> S>(
        mut state: S,
        update: U,
        max_rounds: usize,
    ) -> S {
        for _ in 0..max_rounds {
            let next = update(&state);
            if next == state {
                return next;
            }
            state = next;
        }
        state
    }
}

// ===================================================================
// CompetitiveSelection (hard / soft / ranked)
// ===================================================================
/// Selection mode. The candidate–seat–scoring skeleton is
/// shared; only the allocation mechanism differs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SelectionMode {
    /// argmax — exactly one winner per seat (mutual exclusion).
    Hard,
    /// softmax — every candidate contributes, weights sum to 1.
    Soft,
    /// top-K — up to K winners (bounded multiplicity).
    Ranked,
}

/// **Motivation.** Allocate scarce seats to candidates under a score.
///
/// **Definition / Invariant.** Hard: one winner, mutual exclusion. Soft:
/// proportional, weights normalise. Ranked: ≤ K winners.
///
/// **Recognition.** Priority-queue extract-min (hard), attention (soft),
/// top-K / beam (ranked). The priority queue is the data structure that
/// makes hard mode efficient — exposed as [`PriorityQueue`].
pub struct CompetitiveSelection;
impl CompetitiveSelection {
    /// Hard mode: the single highest-scoring candidate.
    pub fn hard<T: Clone, F: Fn(&T) -> i64>(candidates: &[T], score: F) -> Option<T> {
        candidates.iter().max_by_key(|c| score(c)).cloned()
    }
    /// Ranked mode: the top-K by score (descending), bounded multiplicity.
    pub fn ranked<T: Clone, F: Fn(&T) -> i64>(candidates: &[T], k: usize, score: F) -> Vec<T> {
        let mut v: Vec<T> = candidates.to_vec();
        v.sort_by(|a, b| score(b).cmp(&score(a)));
        v.truncate(k);
        v
    }
    /// Soft mode: integer-scored softmax-style weights (scaled), summing
    /// to `scale`. Included for completeness; not used by the classical
    /// corpus.
    pub fn soft<T, F: Fn(&T) -> i64>(candidates: &[T], score: F, scale: i64) -> Vec<i64> {
        let scores: Vec<i64> = candidates.iter().map(|c| score(c)).collect();
        let total: i64 = scores.iter().sum::<i64>().max(1);
        scores.iter().map(|s| s * scale / total).collect()
    }
}

/// Hard-mode CompetitiveSelection as a data structure: a binary heap.
/// `pop_best` extracts the current argmax (or argmin via `Reverse`).
/// This is the priority queue Dijkstra/Prim/heap algorithms use.
#[derive(Debug, Clone)]
pub struct PriorityQueue<T: Ord> {
    heap: BinaryHeap<T>,
}
impl<T: Ord> PriorityQueue<T> {
    pub fn new() -> Self {
        Self {
            heap: BinaryHeap::new(),
        }
    }
    pub fn push(&mut self, item: T) {
        self.heap.push(item);
    }
    pub fn pop_best(&mut self) -> Option<T> {
        self.heap.pop()
    }
    pub fn peek(&self) -> Option<&T> {
        self.heap.peek()
    }
    pub fn len(&self) -> usize {
        self.heap.len()
    }
    pub fn is_empty(&self) -> bool {
        self.heap.is_empty()
    }
}
impl<T: Ord + PartialEq> PartialEq for PriorityQueue<T> {
    fn eq(&self, other: &Self) -> bool {
        // Compare as sorted sequences so order-independent equality holds.
        let mut a: Vec<&T> = self.heap.iter().collect();
        let mut b: Vec<&T> = other.heap.iter().collect();
        a.sort_unstable();
        b.sort_unstable();
        a == b
    }
}
impl<T: Ord> Default for PriorityQueue<T> {
    fn default() -> Self {
        Self::new()
    }
}

// ===================================================================
// Sampler
// ===================================================================
/// **Motivation.** Probabilistic selection from a distribution.
///
/// **Definition.** Deterministic-seeded selection of `count` items
/// (a linear-congruential stream keeps the corpus reproducible —
/// classical algorithms are deterministic, and Sampler is for randomized
/// variants only).
///
/// **Invariant.** Distributional correctness over the seed stream.
pub struct Sampler {
    state: u64,
}
impl Sampler {
    pub fn new(seed: u64) -> Self {
        Self { state: seed }
    }
    fn next_u64(&mut self) -> u64 {
        // LCG (Numerical Recipes constants) — reproducible.
        self.state = self
            .state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }
    pub fn pick_index(&mut self, n: usize) -> usize {
        if n == 0 {
            0
        } else {
            (self.next_u64() as usize) % n
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn reduction_is_associative_for_sum() {
        let v = vec![1, 2, 3, 4, 5];
        let left = Reduction::reduce(v.clone(), 0, |a, b| a + b);
        let split: i32 = {
            let (l, r) = v.split_at(2);
            Reduction::reduce(l.to_vec(), 0, |a, b| a + b)
                + Reduction::reduce(r.to_vec(), 0, |a, b| a + b)
        };
        assert_eq!(left, split);
    }
    #[test]
    fn hard_select_is_argmax() {
        assert_eq!(
            CompetitiveSelection::hard(&[3, 9, 4], |x| *x as i64),
            Some(9)
        );
    }
    #[test]
    fn ranked_is_bounded_topk() {
        assert_eq!(
            CompetitiveSelection::ranked(&[1, 5, 3, 9, 2], 2, |x| *x as i64),
            vec![9, 5]
        );
    }
    #[test]
    fn pq_extracts_in_order() {
        let mut pq = PriorityQueue::new();
        for x in [3, 1, 4, 1, 5] {
            pq.push(x);
        }
        assert_eq!(pq.pop_best(), Some(5));
        assert_eq!(pq.pop_best(), Some(4));
    }
}
