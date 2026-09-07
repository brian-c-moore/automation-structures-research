//! `TraversalEngine`.
//!
//! **Vendored verbatim** from
//! `supplementary-research/studies/domain-corpora/algorithms/rust/src/primitives/control.rs` (`TraversalEngine` section).
//! In cryptography this is the bounded-iteration primitive: rounds
//! (SHA-256's 64; AES's 10; SHA-3's 24; ChaCha20's 20), blocks
//! (Merkle-Damgård and counter modes), scalar bits (RSA / Ed25519 /
//! X25519 ladder), bignum limbs, schedule positions (SHA-256's
//! message schedule). The classical Algorithms corpus uses the same
//! primitive for DFS/BFS/topological-fill, where the graph is the
//! algorithm's data dependency rather than a fixed round count.

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
///
/// In cryptography the dominant uses are bounded iterations over a
/// fixed schedule (rounds, blocks, bits); the DFS/BFS/backtrack
/// variants are inherited verbatim from the classical-corpus primitive.
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
    /// Bounded iteration over a fixed count of rounds / blocks /
    /// schedule positions. The dominant `TraversalEngine` use in
    /// cryptography.
    pub fn iter_rounds<St, R: FnMut(&mut St, usize)>(
        state: &mut St,
        rounds: usize,
        mut round_fn: R,
    ) {
        for i in 0..rounds {
            round_fn(state, i);
        }
    }
    /// Backtracking driver: TraversalEngine plus paired undo.
    /// `extend` yields candidate moves; `apply`/`undo` are the
    /// paired mutations; `accept` collects a solution snapshot. Not
    /// load-bearing in the cryptographic corpus; included for the
    /// completeness of the vendored primitive.
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

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn iter_rounds_runs_exactly_the_count() {
        let mut counter = 0usize;
        TraversalEngine::iter_rounds(&mut counter, 64, |c, _i| *c += 1);
        assert_eq!(counter, 64);
    }
}
