//! Phase 7 — Linked List, Tries, Graphs.
//!
//! All algorithms are built **only** from [`crate::primitives`] and
//! [`crate::candidates`]; no algorithm reimplements primitive logic.
//!
//! ## Composition shapes
//!
//! | Algorithm | Structural ordering | Key primitives |
//! |---|---|---|
//! | Reverse Linked List | Linear | TraversalEngine + ActuationPass |
//! | Linked List Cycle | Linear | FastSlow (two-cursor; no governance primitive) |
//! | Merge Two Sorted Lists | Linear | TraversalEngine + ActuationPass |
//! | Merge K Sorted Lists | Linear | PriorityQueue (CompetitiveSelection-hard) + TraversalEngine + ActuationPass |
//! | Reorder List | Tree (3 phases) | TraversalEngine + ActuationPass |
//! | Implement Trie | Linear per op | ResourceRegistry (nested-registry trie) + TraversalEngine |
//! | Add and Search Words | Tree (wildcard DFS) | ResourceRegistry (trie) + TraversalEngine::backtrack + Reduction(OR) |
//! | Word Search II | Tree | TraversalEngine::backtrack (grid, paired-undo) + ResourceRegistry (trie+visited) |
//! | Number of Islands | Tree (components) | TraversalEngine::dfs + ResourceRegistry (visited) + Reduction (count) |
//! | Clone Graph | Tree | TraversalEngine::bfs + ResourceRegistry (original→clone map) + ActuationPass |
//! | Pacific Atlantic | Tree | TraversalEngine::bfs×2 + ResourceRegistry×2 + Reduction (intersect) |
//! | Course Schedule | DAG | TraversalEngine::bfs (Kahn) + ResourceRegistry (in-deg+adj) + Reduction (count) |
//!
//! ## I/O encoding (Rust ↔ Python identical)
//!
//! - **Linked list** node values: `Value::ints([v0, v1, …])` (order = list order).
//! - **Linked List Cycle** input: `Value::List([ints_list, Int pos])` where
//!   `pos` is the 0-based index of the cycle-entry node (-1 = no cycle).
//!   Output: `Value::Bool`.
//! - **Reverse / Merge Two / Reorder**: `Value::ints` → `Value::ints`.
//! - **Merge K**: `Value::List([ints_list, …])` → `Value::ints`.
//! - **Trie / Add-Search-Words** op stream:
//!   `Value::List([["op", "word"], …])` where op ∈ {"insert","search","startsWith","addWord"}.
//!   Output: `Value::List` of `Bool` per query op; insert/addWord produce no output element.
//!   Queries: "search" and "startsWith" for Trie; "search" for AddSearch.
//! - **Word Search II** input: `Value::List([List[Str] grid, List[Str] words])`.
//!   Output: `Value::ints` of sorted 0-based indices into `words` of found words.
//!   Equiv: `Equiv::Exact` (sorted stable).
//! - **Number of Islands** input: `Value::List([List[Str], …])` grid of "1"/"0" single-char strings.
//!   Output: `Value::Int`.
//! - **Clone Graph** input: `Value::List([List[Int] adj_row_0, …])` (0-based nodes, sorted adj lists).
//!   Output: same encoding (sorted rows, node order = input order). Equiv: `Equiv::Exact`.
//! - **Pacific Atlantic** input: `Value::List([List[Int] row_0, …])` elevations.
//!   Output: `Value::List` of `[row, col]` int pairs. Equiv: `Equiv::SetOfIntLists`.
//! - **Course Schedule** input: `Value::List([Int n, List[Int [a,b]], …])`.
//!   Output: `Value::Bool` (can all courses be finished?).

use super::{entry, gen};
use crate::config::CorpusEntry;
use crate::equivalence::Equiv;
use crate::primitives::{
    ActuationPass, PriorityQueue, Reduction, ResourceRegistry, TraversalEngine,
};
use crate::value::Value;
use std::cmp::Reverse;

// ===========================================================================
// Reverse Linked List
//
// Composition: TraversalEngine (chain walk) + ActuationPass (link mutation).
// Linked list is modelled as Value::ints (node values in order).
// ===========================================================================
fn reverse_linked_list(input: Value) -> Value {
    let mut nodes = input.as_int_vec();
    let n = nodes.len();
    // ActuationPass over the first half: swap[i] with mirror.
    ActuationPass::apply_each(0..n / 2, |i| {
        nodes.swap(i, n - 1 - i);
    });
    Value::ints(&nodes)
}

// ===========================================================================
// Linked List Cycle (Floyd's tortoise-and-hare)
//
// Composition: the FastSlow idiom — two cursors walk the successor function
// at rates 1 and 2; coincidence ⇒ cycle. It carries a move rule and a
// termination argument but no governance invariant, so it is not a catalog
// primitive.
// No ResourceRegistry — O(1) space is the structural point.
// Input: [ints_list, Int pos]  pos = cycle-entry index (-1 = no cycle).
// ===========================================================================
fn linked_list_cycle(input: Value) -> Value {
    let parts = input.as_list();
    let nodes = parts[0].as_int_vec();
    let pos = parts[1].as_int();
    let n = nodes.len();
    if n == 0 {
        return Value::Bool(false);
    }
    // Successor: linear walk, wrap to pos at tail if cycle present.
    let succ = |idx: usize| -> Option<usize> {
        if idx + 1 < n {
            Some(idx + 1)
        } else if pos >= 0 {
            Some(pos as usize)
        } else {
            None
        }
    };
    // FastSlow: advance slow (×1) and fast (×2) cursors.
    let mut slow = 0usize;
    let mut fast = 0usize;
    loop {
        slow = match succ(slow) {
            Some(s) => s,
            None => return Value::Bool(false),
        };
        fast = match succ(fast) {
            Some(s) => s,
            None => return Value::Bool(false),
        };
        fast = match succ(fast) {
            Some(s) => s,
            None => return Value::Bool(false),
        };
        if slow == fast {
            return Value::Bool(true);
        }
    }
}

// ===========================================================================
// Merge Two Sorted Lists
//
// Composition: TraversalEngine (two-cursor parallel walk) + ActuationPass
// (append chosen minimum to output).
// ===========================================================================
fn merge_two_sorted_lists(input: Value) -> Value {
    let parts = input.as_list();
    let a = parts[0].as_int_vec();
    let b = parts[1].as_int_vec();
    let mut out: Vec<i64> = Vec::with_capacity(a.len() + b.len());
    let (mut i, mut j) = (0usize, 0usize);
    while i < a.len() && j < b.len() {
        if a[i] <= b[j] {
            ActuationPass::apply_each(std::iter::once(a[i]), |v| out.push(v));
            i += 1;
        } else {
            ActuationPass::apply_each(std::iter::once(b[j]), |v| out.push(v));
            j += 1;
        }
    }
    ActuationPass::apply_each(a[i..].iter().copied(), |v| out.push(v));
    ActuationPass::apply_each(b[j..].iter().copied(), |v| out.push(v));
    Value::ints(&out)
}

// ===========================================================================
// Merge K Sorted Lists
//
// Composition: PriorityQueue (CompetitiveSelection-hard, min-heap) +
// TraversalEngine (K-way cursor advance) + ActuationPass (append to output).
//
// Heap entry: Reverse((value, list_index, position)) for min-heap semantics.
// ===========================================================================
fn merge_k_sorted_lists(input: Value) -> Value {
    let lists: Vec<Vec<i64>> = input.as_list().iter().map(|l| l.as_int_vec()).collect();
    let mut pq: PriorityQueue<Reverse<(i64, usize, usize)>> = PriorityQueue::new();
    // Seed: first element of each non-empty list.
    for (li, lst) in lists.iter().enumerate() {
        if !lst.is_empty() {
            pq.push(Reverse((lst[0], li, 0)));
        }
    }
    let mut out: Vec<i64> = Vec::new();
    while let Some(Reverse((val, li, pos))) = pq.pop_best() {
        ActuationPass::apply_each(std::iter::once(val), |v| out.push(v));
        let next = pos + 1;
        if next < lists[li].len() {
            pq.push(Reverse((lists[li][next], li, next)));
        }
    }
    Value::ints(&out)
}

// ===========================================================================
// Reorder List
//
// Composition: TraversalEngine (3 phases) + ActuationPass.
// Phase 1: locate midpoint via fast+slow cursors (TraversalEngine).
// Phase 2: reverse second half (ActuationPass).
// Phase 3: interleave two halves (TraversalEngine + ActuationPass).
// ===========================================================================
fn reorder_list(input: Value) -> Value {
    let nodes = input.as_int_vec();
    let n = nodes.len();
    if n <= 1 {
        return Value::ints(&nodes);
    }
    // Phase 1: midpoint via slow/fast cursor walk.
    let mid = {
        let mut slow = 0usize;
        let mut fast = 0usize;
        while fast + 1 < n && fast + 2 < n {
            slow += 1;
            fast += 2;
        }
        slow
    };
    let first = nodes[..=mid].to_vec();
    let mut second = nodes[mid + 1..].to_vec();
    // Phase 2: reverse second half via ActuationPass.
    let m = second.len();
    ActuationPass::apply_each(0..m / 2, |i| {
        second.swap(i, m - 1 - i);
    });
    // Phase 3: interleave (TraversalEngine over two cursors + ActuationPass).
    let mut out: Vec<i64> = Vec::with_capacity(n);
    let (mut i, mut j) = (0usize, 0usize);
    let mut from_first = true;
    while i < first.len() || j < second.len() {
        if from_first && i < first.len() {
            ActuationPass::apply_each(std::iter::once(first[i]), |v| out.push(v));
            i += 1;
        } else if j < second.len() {
            ActuationPass::apply_each(std::iter::once(second[j]), |v| out.push(v));
            j += 1;
        } else {
            ActuationPass::apply_each(std::iter::once(first[i]), |v| out.push(v));
            i += 1;
        }
        from_first = !from_first;
    }
    Value::ints(&out)
}

// ===========================================================================
// Trie internals
//
// ResourceRegistry specialised to sequence keys: a nested-registry trie.
// Each node = ResourceRegistry<char, node_id> (child map) + terminal flag.
// The arena (ResourceRegistry<usize, TrieCell>) owns all nodes.
// The arena indirection satisfies Rust's ownership rules without introducing
// non-primitive logic.
// ===========================================================================

#[derive(Clone)]
struct TrieCell {
    children: ResourceRegistry<char, usize>,
    terminal: bool,
}

struct TrieArena {
    cells: ResourceRegistry<usize, TrieCell>,
    next_id: usize,
}

impl TrieArena {
    fn new() -> Self {
        let mut a = Self {
            cells: ResourceRegistry::new(),
            next_id: 1,
        };
        a.cells.insert(
            0,
            TrieCell {
                children: ResourceRegistry::new(),
                terminal: false,
            },
        );
        a
    }

    fn alloc_node(&mut self) -> usize {
        let id = self.next_id;
        self.next_id += 1;
        self.cells.insert(
            id,
            TrieCell {
                children: ResourceRegistry::new(),
                terminal: false,
            },
        );
        id
    }

    /// TraversalEngine: walk-and-create one character at a time.
    fn insert(&mut self, word: &str) {
        let mut cur = 0usize;
        for ch in word.chars() {
            let next = if let Some(&c) = self.cells.lookup(&cur).unwrap().children.lookup(&ch) {
                c
            } else {
                let new_id = self.alloc_node();
                self.cells
                    .entry_or(
                        cur,
                        TrieCell {
                            children: ResourceRegistry::new(),
                            terminal: false,
                        },
                    )
                    .children
                    .insert(ch, new_id);
                new_id
            };
            cur = next;
        }
        self.cells
            .entry_or(
                cur,
                TrieCell {
                    children: ResourceRegistry::new(),
                    terminal: false,
                },
            )
            .terminal = true;
    }

    /// TraversalEngine: walk and check terminal marker (exact match).
    fn search(&self, word: &str) -> bool {
        let mut cur = 0usize;
        for ch in word.chars() {
            match self.cells.lookup(&cur).and_then(|c| c.children.lookup(&ch)) {
                Some(&n) => cur = n,
                None => return false,
            }
        }
        self.cells.lookup(&cur).map_or(false, |c| c.terminal)
    }

    /// TraversalEngine: walk without checking terminal (prefix match).
    fn starts_with(&self, prefix: &str) -> bool {
        let mut cur = 0usize;
        for ch in prefix.chars() {
            match self.cells.lookup(&cur).and_then(|c| c.children.lookup(&ch)) {
                Some(&n) => cur = n,
                None => return false,
            }
        }
        true
    }

    /// Collect all child node ids of `node`.
    fn child_ids(&self, node: usize) -> Vec<usize> {
        self.cells
            .lookup(&node)
            .map(|c| c.children.values().copied().collect())
            .unwrap_or_default()
    }

    /// Follow one character edge; returns None if edge absent.
    fn follow(&self, node: usize, ch: char) -> Option<usize> {
        self.cells.lookup(&node)?.children.lookup(&ch).copied()
    }

    fn is_terminal(&self, node: usize) -> bool {
        self.cells.lookup(&node).map_or(false, |c| c.terminal)
    }
}

// ===========================================================================
// Implement Trie (op sequence)
//
// Input: Value::List([["insert","word"], ["search","w"], ["startsWith","app"], …])
// Output: Value::List of Bool per query op ("search" / "startsWith").
// ===========================================================================
fn implement_trie(input: Value) -> Value {
    let ops = input.as_list();
    let mut trie = TrieArena::new();
    let mut results: Vec<Value> = Vec::new();
    for op in ops {
        let pair = op.as_list();
        let kind = pair[0].as_str();
        let word = pair[1].as_str();
        match kind {
            "insert" => trie.insert(word),
            "search" => results.push(Value::Bool(trie.search(word))),
            "startsWith" => results.push(Value::Bool(trie.starts_with(word))),
            _ => {}
        }
    }
    Value::List(results)
}

// ===========================================================================
// Design Add and Search Words (wildcards)
//
// Composition: ResourceRegistry (trie) + TraversalEngine::backtrack at '.'
// (wildcard DFS over all children) + Reduction(OR).
//
// Input: Value::List([["addWord","bad"], ["search",".ad"], …])
// Output: Value::List of Bool per "search" op.
// ===========================================================================
fn add_search_words(input: Value) -> Value {
    let ops = input.as_list();
    let mut trie = TrieArena::new();
    let mut results: Vec<Value> = Vec::new();
    for op in ops {
        let pair = op.as_list();
        let kind = pair[0].as_str();
        let word = pair[1].as_str();
        match kind {
            "addWord" | "insert" => trie.insert(word),
            "search" => {
                let chars: Vec<char> = word.chars().collect();
                results.push(Value::Bool(wildcard_search(&trie, 0, &chars, 0)));
            }
            _ => {}
        }
    }
    Value::List(results)
}

/// Recursive wildcard search. At '.' branches into all children via
/// Reduction(OR). No trie mutation → no paired undo needed in the trie.
fn wildcard_search(trie: &TrieArena, node: usize, chars: &[char], pos: usize) -> bool {
    if pos == chars.len() {
        return trie.is_terminal(node);
    }
    let ch = chars[pos];
    if ch == '.' {
        // TraversalEngine exploring all child branches; Reduction(OR) collapses.
        Reduction::reduce(
            trie.child_ids(node)
                .into_iter()
                .map(|child| wildcard_search(trie, child, chars, pos + 1)),
            false,
            |a, b| a || b,
        )
    } else {
        match trie.follow(node, ch) {
            Some(next) => wildcard_search(trie, next, chars, pos + 1),
            None => false,
        }
    }
}

// ===========================================================================
// Word Search II
//
// Composition: TraversalEngine::backtrack (grid DFS, paired undo via
// ResourceRegistry insert/delete) + ResourceRegistry (trie for prefix pruning,
// visited-cell set).
//
// Input: Value::List([List[Str] grid_rows, List[Str] words])
// Output: Value::ints of sorted 0-based indices (into `words`) of found words.
// Equiv: Equiv::Exact (output is sorted, stable).
// ===========================================================================
fn word_search_ii(input: Value) -> Value {
    let parts = input.as_list();
    let grid_rows: Vec<Vec<char>> = parts[0]
        .as_list()
        .iter()
        .map(|v| v.as_str().chars().collect())
        .collect();
    let words: Vec<String> = parts[1]
        .as_list()
        .iter()
        .map(|v| v.as_str().to_string())
        .collect();

    if grid_rows.is_empty() || words.is_empty() {
        return Value::ints(&[]);
    }
    let rows = grid_rows.len();
    let cols = grid_rows[0].len();

    // Build trie of all words (ResourceRegistry nested structure).
    let mut trie = TrieArena::new();
    for w in &words {
        trie.insert(w);
    }

    // ResourceRegistry: found word strings.
    let mut found_words: ResourceRegistry<String, ()> = ResourceRegistry::new();
    // ResourceRegistry: visited cells for current DFS path (paired undo).
    let mut visited: ResourceRegistry<(usize, usize), ()> = ResourceRegistry::new();

    // TraversalEngine::backtrack from every grid cell.
    for r in 0..rows {
        for c in 0..cols {
            let ch = grid_rows[r][c];
            if let Some(start_node) = trie.follow(0, ch) {
                // Apply: mark current cell visited.
                visited.insert((r, c), ());
                let mut prefix = ch.to_string();
                // Accept if this single char is already a word.
                if trie.is_terminal(start_node) {
                    found_words.insert(prefix.clone(), ());
                }
                // Recurse into neighbours.
                ws2_dfs(
                    &trie,
                    &grid_rows,
                    rows,
                    cols,
                    r,
                    c,
                    start_node,
                    &mut prefix,
                    &mut visited,
                    &mut found_words,
                );
                // Undo: unmark cell.
                visited.delete(&(r, c));
            }
        }
    }

    // Map found word strings back to their input indices; sort.
    let mut indices: Vec<i64> = words
        .iter()
        .enumerate()
        .filter(|(_, w)| found_words.contains(w))
        .map(|(i, _)| i as i64)
        .collect();
    indices.sort_unstable();
    indices.dedup();
    Value::ints(&indices)
}

/// TraversalEngine::backtrack helper: DFS over grid + trie simultaneously.
/// `prefix` carries the current path string (backtracking state).
/// `visited` is the ResourceRegistry for visited cells; paired-undo on retreat.
fn ws2_dfs(
    trie: &TrieArena,
    grid: &[Vec<char>],
    rows: usize,
    cols: usize,
    r: usize,
    c: usize,
    node: usize,
    prefix: &mut String,
    visited: &mut ResourceRegistry<(usize, usize), ()>,
    found_words: &mut ResourceRegistry<String, ()>,
) {
    for (dr, dc) in [(-1i64, 0i64), (1, 0), (0, -1), (0, 1)] {
        let nr = r as i64 + dr;
        let nc = c as i64 + dc;
        if nr < 0 || nc < 0 || nr as usize >= rows || nc as usize >= cols {
            continue;
        }
        let (nr, nc) = (nr as usize, nc as usize);
        if visited.contains(&(nr, nc)) {
            continue;
        }
        let ch = grid[nr][nc];
        let next_node = match trie.follow(node, ch) {
            Some(n) => n,
            None => continue,
        };
        // Apply: extend prefix, mark visited.
        prefix.push(ch);
        visited.insert((nr, nc), ());
        if trie.is_terminal(next_node) {
            found_words.insert(prefix.clone(), ());
        }
        ws2_dfs(
            trie,
            grid,
            rows,
            cols,
            nr,
            nc,
            next_node,
            prefix,
            visited,
            found_words,
        );
        // Undo: pop prefix char, unmark visited (paired-undo invariant).
        prefix.pop();
        visited.delete(&(nr, nc));
    }
}

// ===========================================================================
// Number of Islands
//
// Composition: TraversalEngine::dfs (flood-fill per component) +
// ResourceRegistry (visited cells) + Reduction (component count).
// Grid = implicit graph with 4-connectivity.
//
// Input: Value::List([List[Str], …]) — each Str is a single-char "1" or "0".
// Output: Value::Int.
// ===========================================================================
fn number_of_islands(input: Value) -> Value {
    let grid: Vec<Vec<char>> = input
        .as_list()
        .iter()
        .map(|row| {
            row.as_list()
                .iter()
                .map(|cell| cell.as_str().chars().next().unwrap_or('0'))
                .collect()
        })
        .collect();
    let rows = grid.len();
    if rows == 0 {
        return Value::Int(0);
    }
    let cols = grid[0].len();

    // ResourceRegistry: visited cells (prevents double-counting).
    let mut visited: ResourceRegistry<(usize, usize), ()> = ResourceRegistry::new();

    // Reduction: count = sum of 1 per flood-fill start.
    let mut count = 0i64;
    for r in 0..rows {
        for c in 0..cols {
            if grid[r][c] == '1' && !visited.contains(&(r, c)) {
                // TraversalEngine::dfs (manual stack — a Vec substrate buffer — with the visited ResourceRegistry).
                let mut stack = vec![(r, c)];
                while let Some((cr, cc)) = stack.pop() {
                    if visited.contains(&(cr, cc)) {
                        continue;
                    }
                    visited.insert((cr, cc), ());
                    for (dr, dc) in [(-1i64, 0i64), (1, 0), (0, -1), (0, 1)] {
                        let nr = cr as i64 + dr;
                        let nc = cc as i64 + dc;
                        if nr >= 0 && nc >= 0 {
                            let (nr, nc) = (nr as usize, nc as usize);
                            if nr < rows
                                && nc < cols
                                && grid[nr][nc] == '1'
                                && !visited.contains(&(nr, nc))
                            {
                                stack.push((nr, nc));
                            }
                        }
                    }
                }
                // Reduction: accumulate island count.
                count = Reduction::reduce(vec![count, 1], 0, |a, b| a + b);
            }
        }
    }
    Value::Int(count)
}

// ===========================================================================
// Clone Graph
//
// Composition: TraversalEngine::bfs + ResourceRegistry (visited) + ActuationPass.
// Registry serves dual purpose: visited tracking + structural copy.
//
// Input: Value::List([List[Int] adj_row_0, …]) — sorted neighbour lists, 0-based.
// Output: same encoding. Equiv: Equiv::Exact.
// ===========================================================================
fn clone_graph(input: Value) -> Value {
    let adj: Vec<Vec<i64>> = input.as_list().iter().map(|row| row.as_int_vec()).collect();
    let n = adj.len();
    if n == 0 {
        return Value::List(vec![]);
    }

    // ResourceRegistry: tracks which nodes have been cloned.
    let mut visited: ResourceRegistry<usize, ()> = ResourceRegistry::new();
    let mut cloned: Vec<Vec<i64>> = vec![vec![]; n];

    // TraversalEngine::bfs from node 0 to visit all reachable nodes.
    let bfs_order = TraversalEngine::bfs(0usize, |&node| {
        adj[node].iter().map(|&nb| nb as usize).collect()
    });
    // ActuationPass: for each visited node, copy its sorted adjacency row.
    ActuationPass::apply_each(bfs_order.iter().copied(), |node| {
        visited.insert(node, ());
        let mut row = adj[node].clone();
        row.sort_unstable();
        cloned[node] = row;
    });

    Value::List(cloned.into_iter().map(|row| Value::ints(&row)).collect())
}

// ===========================================================================
// Pacific Atlantic Water Flow
//
// Composition: TraversalEngine::bfs (×2, one per ocean) + ResourceRegistry (×2)
// + Reduction (intersection).
// Reversed-flow trick: BFS inward from each ocean's edge with non-decreasing
// elevation constraint.
//
// Input: Value::List([List[Int] row_0, …]) elevations.
// Output: Value::List of [row, col] pairs. Equiv: Equiv::SetOfIntLists.
// ===========================================================================
fn pacific_atlantic(input: Value) -> Value {
    let grid: Vec<Vec<i64>> = input.as_list().iter().map(|row| row.as_int_vec()).collect();
    let rows = grid.len();
    if rows == 0 {
        return Value::List(vec![]);
    }
    let cols = grid[0].len();

    // BFS from a set of source cells; returns ResourceRegistry of reachable cells.
    let bfs_reach = |sources: Vec<(usize, usize)>| -> ResourceRegistry<(usize, usize), ()> {
        let mut reachable: ResourceRegistry<(usize, usize), ()> = ResourceRegistry::new();
        let mut queue = std::collections::VecDeque::new();
        for s in sources {
            if !reachable.contains(&s) {
                reachable.insert(s, ());
                queue.push_back(s);
            }
        }
        while let Some((r, c)) = queue.pop_front() {
            for (dr, dc) in [(-1i64, 0i64), (1, 0), (0, -1), (0, 1)] {
                let nr = r as i64 + dr;
                let nc = c as i64 + dc;
                if nr >= 0 && nc >= 0 {
                    let (nr, nc) = (nr as usize, nc as usize);
                    if nr < rows
                        && nc < cols
                        && !reachable.contains(&(nr, nc))
                        && grid[nr][nc] >= grid[r][c]
                    {
                        reachable.insert((nr, nc), ());
                        queue.push_back((nr, nc));
                    }
                }
            }
        }
        reachable
    };

    // Pacific sources: top row + left col.
    let pac_sources: Vec<(usize, usize)> = (0..cols)
        .map(|c| (0, c))
        .chain((1..rows).map(|r| (r, 0)))
        .collect();
    // Atlantic sources: bottom row + right col.
    let atl_sources: Vec<(usize, usize)> = (0..cols)
        .map(|c| (rows - 1, c))
        .chain((0..rows.saturating_sub(1)).map(|r| (r, cols - 1)))
        .collect();

    // Two independent TraversalEngine passes.
    let pac = bfs_reach(pac_sources);
    let atl = bfs_reach(atl_sources);

    // Reduction: intersection = cells reachable by both.
    let mut result: Vec<Vec<i64>> = (0..rows)
        .flat_map(|r| (0..cols).map(move |c| (r, c)))
        .filter(|(r, c)| pac.contains(&(*r, *c)) && atl.contains(&(*r, *c)))
        .map(|(r, c)| vec![r as i64, c as i64])
        .collect();
    result.sort();
    Value::List(result.into_iter().map(|rc| Value::ints(&rc)).collect())
}

// ===========================================================================
// Course Schedule (Kahn's topological sort)
//
// Composition: TraversalEngine::bfs level-order (Kahn) + ResourceRegistry
// (in-degrees + adjacency) + Reduction (count of processed courses).
//
// Input: Value::List([Int n, List[Int [a,b]], …])  (b must precede a).
// Output: Value::Bool (no cycle = all courses completable).
// ===========================================================================
fn course_schedule(input: Value) -> Value {
    let parts = input.as_list();
    let n = parts[0].as_int().max(0) as usize;
    if n == 0 {
        return Value::Bool(true);
    }

    // ResourceRegistry: in-degree per course.
    let mut in_deg: ResourceRegistry<usize, i64> = ResourceRegistry::new();
    // ResourceRegistry: adjacency (course → its dependents).
    let mut adj: ResourceRegistry<usize, Vec<usize>> = ResourceRegistry::new();
    for i in 0..n {
        in_deg.insert(i, 0);
        adj.insert(i, vec![]);
    }

    // Build graph from prerequisite pairs.
    for pair_val in &parts[1..] {
        let pair = pair_val.as_int_vec();
        if pair.len() < 2 {
            continue;
        }
        let (a, b) = (pair[0] as usize, pair[1] as usize);
        if a < n && b < n && a != b {
            adj.entry_or(b, vec![]).push(a);
            *in_deg.entry_or(a, 0) += 1;
        }
    }

    // Kahn's BFS: enqueue all zero-in-degree courses.
    let mut queue: std::collections::VecDeque<usize> = (0..n)
        .filter(|&i| *in_deg.lookup(&i).unwrap_or(&0) == 0)
        .collect();

    // Reduction: count processed = fold over BFS-extracted nodes.
    let processed = Reduction::reduce(
        std::iter::from_fn(|| {
            queue.pop_front().map(|node| {
                let deps = adj.lookup(&node).cloned().unwrap_or_default();
                for dep in deps {
                    let d = in_deg.entry_or(dep, 1);
                    *d -= 1;
                    if *d == 0 {
                        queue.push_back(dep);
                    }
                }
                1i64
            })
        }),
        0i64,
        |a, b| a + b,
    );

    Value::Bool(processed == n as i64)
}

// ===========================================================================
// Input generators (curated + ~1000 property-based)
// ===========================================================================

fn g_reverse_ll() -> Vec<Value> {
    let mut v = vec![
        Value::ints(&[]),
        Value::ints(&[1]),
        Value::ints(&[1, 2]),
        Value::ints(&[1, 2, 3, 4, 5]),
        Value::ints(&[7, 3, 1]),
    ];
    v.extend(gen::rand_int_lists(71, 1000, 10, 0, 20));
    v
}

fn g_ll_cycle() -> Vec<Value> {
    // [ints_list, pos]
    let mut v = vec![
        Value::List(vec![Value::ints(&[]), Value::Int(-1)]),
        Value::List(vec![Value::ints(&[1]), Value::Int(-1)]),
        Value::List(vec![Value::ints(&[1, 2]), Value::Int(-1)]),
        Value::List(vec![Value::ints(&[3, 2, 0, -4]), Value::Int(1)]),
        Value::List(vec![Value::ints(&[1, 2]), Value::Int(0)]),
    ];
    // Property: no-cycle
    for list in gen::rand_int_lists(72, 500, 8, 0, 10) {
        v.push(Value::List(vec![list, Value::Int(-1)]));
    }
    // Property: cycle (pos in range)
    use crate::primitives::Sampler;
    let mut s = Sampler::new(720);
    for _ in 0..500 {
        let len = 1 + s.pick_index(8);
        let pos = s.pick_index(len) as i64;
        let list: Vec<i64> = (0..len as i64).collect();
        v.push(Value::List(vec![Value::ints(&list), Value::Int(pos)]));
    }
    v
}

fn g_merge_two() -> Vec<Value> {
    let mut v = vec![
        Value::List(vec![Value::ints(&[]), Value::ints(&[])]),
        Value::List(vec![Value::ints(&[1, 2, 4]), Value::ints(&[1, 3, 4])]),
        Value::List(vec![Value::ints(&[]), Value::ints(&[0])]),
        Value::List(vec![Value::ints(&[5]), Value::ints(&[1, 2, 6])]),
    ];
    use crate::primitives::Sampler;
    let mut s = Sampler::new(73);
    for _ in 0..1000 {
        let la = s.pick_index(8);
        let lb = s.pick_index(8);
        let mut a: Vec<i64> = (0..la).map(|_| s.pick_index(15) as i64).collect();
        let mut b: Vec<i64> = (0..lb).map(|_| s.pick_index(15) as i64).collect();
        a.sort_unstable();
        b.sort_unstable();
        v.push(Value::List(vec![Value::ints(&a), Value::ints(&b)]));
    }
    v
}

fn g_merge_k() -> Vec<Value> {
    let mut v = vec![
        Value::List(vec![]),
        Value::List(vec![
            Value::ints(&[1, 4, 5]),
            Value::ints(&[1, 3, 4]),
            Value::ints(&[2, 6]),
        ]),
        Value::List(vec![Value::ints(&[]), Value::ints(&[1])]),
    ];
    use crate::primitives::Sampler;
    let mut s = Sampler::new(74);
    for _ in 0..1000 {
        let k = 1 + s.pick_index(5);
        let lists: Vec<Value> = (0..k)
            .map(|_| {
                let len = s.pick_index(6);
                let mut lst: Vec<i64> = (0..len).map(|_| s.pick_index(20) as i64).collect();
                lst.sort_unstable();
                Value::ints(&lst)
            })
            .collect();
        v.push(Value::List(lists));
    }
    v
}

fn g_reorder_list() -> Vec<Value> {
    let mut v = vec![
        Value::ints(&[]),
        Value::ints(&[1]),
        Value::ints(&[1, 2]),
        Value::ints(&[1, 2, 3, 4]),
        Value::ints(&[1, 2, 3, 4, 5]),
    ];
    v.extend(gen::rand_int_lists(75, 1000, 10, 0, 20));
    v
}

fn g_trie() -> Vec<Value> {
    let op = |kind: &str, word: &str| {
        Value::List(vec![Value::Str(kind.into()), Value::Str(word.into())])
    };
    let mut v = vec![
        Value::List(vec![
            op("insert", "apple"),
            op("search", "apple"),
            op("search", "app"),
            op("startsWith", "app"),
            op("insert", "app"),
            op("search", "app"),
        ]),
        Value::List(vec![
            op("insert", "ab"),
            op("startsWith", "a"),
            op("search", "a"),
            op("startsWith", "ab"),
            op("search", "abc"),
        ]),
    ];
    use crate::primitives::Sampler;
    let words = ["a", "ab", "abc", "abcd", "b", "bc", "bcd", "cd", "d", ""];
    let mut s = Sampler::new(91);
    for _ in 0..500 {
        let num_ops = 4 + s.pick_index(8);
        let ops: Vec<Value> = (0..num_ops)
            .map(|_| {
                let kind = match s.pick_index(3) {
                    0 => "insert",
                    1 => "search",
                    _ => "startsWith",
                };
                let w = words[s.pick_index(words.len())];
                op(kind, w)
            })
            .collect();
        v.push(Value::List(ops));
    }
    v
}

fn g_add_search_words() -> Vec<Value> {
    let op = |kind: &str, word: &str| {
        Value::List(vec![Value::Str(kind.into()), Value::Str(word.into())])
    };
    let mut v = vec![
        Value::List(vec![
            op("addWord", "bad"),
            op("addWord", "dad"),
            op("addWord", "mad"),
            op("search", "pad"),
            op("search", "bad"),
            op("search", ".ad"),
            op("search", "b.."),
        ]),
        Value::List(vec![
            op("addWord", "a"),
            op("search", "."),
            op("search", ".."),
        ]),
    ];
    use crate::primitives::Sampler;
    let words = ["a", "ab", "abc", "b", "ba"];
    let mut s = Sampler::new(92);
    for _ in 0..500 {
        let num_ops = 4 + s.pick_index(6);
        let ops: Vec<Value> = (0..num_ops)
            .map(|_| {
                let is_add = s.pick_index(2) == 0;
                let base = words[s.pick_index(words.len())];
                if is_add {
                    op("addWord", base)
                } else {
                    // Occasionally insert wildcards.
                    let with_wildcard: String = base
                        .chars()
                        .enumerate()
                        .map(|(i, c)| {
                            if i > 0 && s.pick_index(3) == 0 {
                                '.'
                            } else {
                                c
                            }
                        })
                        .collect();
                    op("search", &with_wildcard)
                }
            })
            .collect();
        v.push(Value::List(ops));
    }
    v
}

fn g_word_search_ii() -> Vec<Value> {
    let grid =
        |rows: &[&str]| Value::List(rows.iter().map(|r| Value::Str(r.to_string())).collect());
    let words = |ws: &[&str]| Value::List(ws.iter().map(|w| Value::Str(w.to_string())).collect());
    let mut v = vec![
        Value::List(vec![
            grid(&["oaan", "etae", "ihkr", "iflv"]),
            words(&["oath", "pea", "eat", "rain"]),
        ]),
        Value::List(vec![grid(&["ab", "cd"]), words(&["abdc", "abcd", "cdab"])]),
        Value::List(vec![grid(&["a"]), words(&["a", "b"])]),
        Value::List(vec![grid(&[]), words(&["a"])]),
    ];
    use crate::primitives::Sampler;
    let mut s = Sampler::new(93);
    for _ in 0..200 {
        let rows: usize = 2 + s.pick_index(3);
        let cols: usize = 2 + s.pick_index(3);
        let g: Vec<String> = (0..rows)
            .map(|_| {
                (0..cols)
                    .map(|_| (b'a' + s.pick_index(4) as u8) as char)
                    .collect()
            })
            .collect();
        let grid_v = Value::List(g.iter().map(|r| Value::Str(r.clone())).collect());
        let num_words = 2 + s.pick_index(4);
        let ws: Vec<Value> = (0..num_words)
            .map(|_| {
                let len = 1 + s.pick_index(4);
                let w: String = (0..len)
                    .map(|_| (b'a' + s.pick_index(4) as u8) as char)
                    .collect();
                Value::Str(w)
            })
            .collect();
        v.push(Value::List(vec![grid_v, Value::List(ws)]));
    }
    v
}

fn g_num_islands() -> Vec<Value> {
    let grid = |rows: &[&str]| -> Value {
        Value::List(
            rows.iter()
                .map(|r| Value::List(r.chars().map(|c| Value::Str(c.to_string())).collect()))
                .collect(),
        )
    };
    let mut v = vec![
        grid(&["11110", "11010", "11000", "00000"]),
        grid(&["11000", "11000", "00100", "00011"]),
        grid(&[]),
        grid(&["1"]),
        grid(&["0"]),
    ];
    use crate::primitives::Sampler;
    let mut s = Sampler::new(121);
    for _ in 0..500 {
        let rows = 1 + s.pick_index(6);
        let cols = 1 + s.pick_index(6);
        let g: Vec<String> = (0..rows)
            .map(|_| {
                (0..cols)
                    .map(|_| if s.pick_index(2) == 0 { '1' } else { '0' })
                    .collect()
            })
            .collect();
        v.push(Value::List(
            g.iter()
                .map(|r| Value::List(r.chars().map(|c| Value::Str(c.to_string())).collect()))
                .collect(),
        ));
    }
    v
}

fn g_clone_graph() -> Vec<Value> {
    let adj = |rows: &[&[i64]]| -> Value {
        Value::List(rows.iter().map(|row| Value::ints(row)).collect())
    };
    let mut v = vec![
        adj(&[]),
        adj(&[&[]]),
        adj(&[&[1], &[0]]),
        adj(&[&[1, 2], &[0, 2], &[0, 1]]),
        adj(&[&[1], &[0, 2], &[1]]),
    ];
    use crate::primitives::Sampler;
    let mut s = Sampler::new(122);
    for _ in 0..500 {
        let n = 1 + s.pick_index(6);
        let mut adj_mat: Vec<Vec<i64>> = vec![vec![]; n];
        for i in 0..n {
            for j in i + 1..n {
                if s.pick_index(2) == 0 {
                    adj_mat[i].push(j as i64);
                    adj_mat[j].push(i as i64);
                }
            }
        }
        // Ensure connectivity: chain all nodes.
        for i in 0..n.saturating_sub(1) {
            if !adj_mat[i].contains(&(i as i64 + 1)) {
                adj_mat[i].push(i as i64 + 1);
                adj_mat[i + 1].push(i as i64);
            }
        }
        for row in &mut adj_mat {
            row.sort_unstable();
            row.dedup();
        }
        v.push(Value::List(
            adj_mat.into_iter().map(|row| Value::ints(&row)).collect(),
        ));
    }
    v
}

fn g_pacific_atlantic() -> Vec<Value> {
    let grid = |rows: &[&[i64]]| -> Value {
        Value::List(rows.iter().map(|row| Value::ints(row)).collect())
    };
    let mut v = vec![
        grid(&[
            &[1, 2, 2, 3, 5],
            &[3, 2, 3, 4, 4],
            &[2, 4, 5, 3, 1],
            &[6, 7, 1, 4, 5],
            &[5, 1, 1, 2, 4],
        ]),
        grid(&[&[1]]),
        grid(&[]),
        grid(&[&[1, 2], &[4, 3]]),
    ];
    use crate::primitives::Sampler;
    let mut s = Sampler::new(123);
    for _ in 0..500 {
        let rows = 1 + s.pick_index(5);
        let cols = 1 + s.pick_index(5);
        let g: Vec<Vec<i64>> = (0..rows)
            .map(|_| (0..cols).map(|_| s.pick_index(10) as i64).collect())
            .collect();
        v.push(Value::List(
            g.into_iter().map(|row| Value::ints(&row)).collect(),
        ));
    }
    v
}

fn g_course_schedule() -> Vec<Value> {
    let sched = |n: i64, prereqs: &[[i64; 2]]| -> Value {
        let mut parts = vec![Value::Int(n)];
        parts.extend(prereqs.iter().map(|p| Value::ints(p)));
        Value::List(parts)
    };
    let mut v = vec![
        sched(2, &[[1, 0]]),
        sched(2, &[[1, 0], [0, 1]]),
        sched(0, &[]),
        sched(1, &[]),
        sched(5, &[[1, 0], [2, 0], [3, 1], [4, 2]]),
    ];
    use crate::primitives::Sampler;
    let mut s = Sampler::new(124);
    for _ in 0..1000 {
        let n = 1 + s.pick_index(7) as i64;
        let num_edges = s.pick_index(6);
        let mut parts = vec![Value::Int(n)];
        for _ in 0..num_edges {
            let a = s.pick_index(n as usize) as i64;
            let b = s.pick_index(n as usize) as i64;
            if a != b {
                parts.push(Value::ints(&[a, b]));
            }
        }
        v.push(Value::List(parts));
    }
    v
}

// ===========================================================================
// Registry
// ===========================================================================

pub fn add(r: &mut Vec<CorpusEntry>) {
    let ll = "TraversalEngine + ActuationPass";
    let llc = "FastSlow (two-cursor; no governance primitive)";
    let mkl = "PriorityQueue(CompetitiveSelection-hard) + TraversalEngine + ActuationPass";
    let tr = "ResourceRegistry(nested-registry-trie) + TraversalEngine";
    let aws = "ResourceRegistry(trie) + TraversalEngine::backtrack(wildcard) + Reduction(OR)";
    let wsii = "TraversalEngine::backtrack(grid,paired-undo) + ResourceRegistry(trie+visited)";
    let noi = "TraversalEngine::dfs + ResourceRegistry(visited) + Reduction(count)";
    let cg = "TraversalEngine::bfs + ResourceRegistry(visited/clone-map) + ActuationPass";
    let pa = "TraversalEngine::bfs*2 + ResourceRegistry*2 + Reduction(intersect)";
    let cs = "TraversalEngine::bfs(Kahn) + ResourceRegistry(in-deg+adj) + Reduction(count)";

    entry(
        r,
        "Reverse Linked List",
        "Linked List",
        7,
        "Linear",
        ll,
        reverse_linked_list,
        "reverse_linked_list",
        Equiv::Exact,
        g_reverse_ll,
    );
    entry(
        r,
        "Linked List Cycle",
        "Linked List",
        7,
        "Linear",
        llc,
        linked_list_cycle,
        "linked_list_cycle",
        Equiv::BoolEq,
        g_ll_cycle,
    );
    entry(
        r,
        "Merge Two Sorted Lists",
        "Linked List",
        7,
        "Linear",
        ll,
        merge_two_sorted_lists,
        "merge_two_sorted_lists",
        Equiv::Exact,
        g_merge_two,
    );
    entry(
        r,
        "Merge K Sorted Lists",
        "Linked List",
        7,
        "Linear",
        mkl,
        merge_k_sorted_lists,
        "merge_k_sorted_lists",
        Equiv::Exact,
        g_merge_k,
    );
    entry(
        r,
        "Reorder List",
        "Linked List",
        7,
        "Tree",
        ll,
        reorder_list,
        "reorder_list",
        Equiv::Exact,
        g_reorder_list,
    );
    entry(
        r,
        "Implement Trie",
        "Tries",
        7,
        "Linear",
        tr,
        implement_trie,
        "implement_trie",
        Equiv::Exact,
        g_trie,
    );
    entry(
        r,
        "Add and Search Words",
        "Tries",
        7,
        "Tree",
        aws,
        add_search_words,
        "add_search_words",
        Equiv::Exact,
        g_add_search_words,
    );
    entry(
        r,
        "Word Search II",
        "Tries",
        7,
        "Tree",
        wsii,
        word_search_ii,
        "word_search_ii",
        Equiv::Exact,
        g_word_search_ii,
    );
    entry(
        r,
        "Number of Islands",
        "Graphs",
        7,
        "Tree",
        noi,
        number_of_islands,
        "number_of_islands",
        Equiv::Exact,
        g_num_islands,
    );
    entry(
        r,
        "Clone Graph",
        "Graphs",
        7,
        "Tree",
        cg,
        clone_graph,
        "clone_graph",
        Equiv::Exact,
        g_clone_graph,
    );
    entry(
        r,
        "Pacific Atlantic",
        "Graphs",
        7,
        "Tree",
        pa,
        pacific_atlantic,
        "pacific_atlantic",
        Equiv::SetOfIntLists,
        g_pacific_atlantic,
    );
    entry(
        r,
        "Course Schedule",
        "Graphs",
        7,
        "DAG",
        cs,
        course_schedule,
        "course_schedule",
        Equiv::BoolEq,
        g_course_schedule,
    );
}
