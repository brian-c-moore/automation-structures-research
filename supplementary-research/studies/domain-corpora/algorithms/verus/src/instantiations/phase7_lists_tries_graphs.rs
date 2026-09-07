// Lists, Tries, Graphs.
//
// Twelve algorithms. Linked lists represented as Vec<i64>; tries as
// flat arena; graphs as adjacency arrays.

use vstd::prelude::*;

verus! {

// ── Reverse Linked List ─────────────────────────────────────
pub uninterp spec fn reverse_linked_list_spec(a: Seq<i64>) -> Seq<i64>;

#[verifier::external_body]
pub fn reverse_linked_list(a: &[i64]) -> (r: Vec<i64>)
    requires a@.len() <= 100_000,
    ensures r@ == reverse_linked_list_spec(a@),
{
    let mut out: Vec<i64> = Vec::new();
    let n = a.len();
    let mut i: i64 = (n as i64) - 1;
    while i >= 0 { out.push(a[i as usize]); i = i - 1; }
    out
}

// ── Linked List Cycle (input: Vec + cycle-entry-index) ──────
// Returns true iff a non-negative cycle index indicates a cycle exists.
pub uninterp spec fn linked_list_cycle_spec(values: Seq<i64>, cycle_entry: i64) -> bool;

#[verifier::external_body]
pub fn linked_list_cycle(values: &[i64], cycle_entry: i64) -> (r: bool)
    requires
        values@.len() <= 10_000,
        cycle_entry >= -1 && cycle_entry < values@.len() as i64,
    ensures r == linked_list_cycle_spec(values@, cycle_entry),
{
    cycle_entry >= 0
}

// ── Merge Two Sorted Lists ──────────────────────────────────
pub uninterp spec fn merge_two_sorted_spec(a: Seq<i64>, b: Seq<i64>) -> Seq<i64>;

#[verifier::external_body]
pub fn merge_two_sorted_lists(a: &[i64], b: &[i64]) -> (r: Vec<i64>)
    requires a@.len() <= 10_000, b@.len() <= 10_000,
    ensures r@ == merge_two_sorted_spec(a@, b@),
{
    let mut out: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    let mut j: usize = 0;
    while i < a.len() || j < b.len() {
        if i < a.len() && (j >= b.len() || a[i] <= b[j]) {
            out.push(a[i]); i = i + 1;
        } else {
            out.push(b[j]); j = j + 1;
        }
    }
    out
}

// ── Merge K Sorted Lists ────────────────────────────────────
// Input: Vec<Vec<i64>> as flat layout (lengths + concatenated values).
pub uninterp spec fn merge_k_sorted_spec(lists: Seq<Seq<i64>>) -> Seq<i64>;

#[verifier::external_body]
pub fn merge_k_sorted_lists(lists: &Vec<Vec<i64>>) -> (r: Vec<i64>)
    requires
        lists@.len() <= 1_000,
        forall|i: int| 0 <= i < lists@.len() ==> lists@[i].len() <= 1_000,
    ensures r@ == merge_k_sorted_spec(Seq::<Seq<i64>>::new(lists@.len(), |k: int| lists@[k]@)),
{
    let mut all: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < lists.len() {
        let mut j: usize = 0;
        while j < lists[i].len() { all.push(lists[i][j]); j = j + 1; }
        i = i + 1;
    }
    all.sort();
    all
}

// ── Reorder List ────────────────────────────────────────────
// Output: L0 → Ln → L1 → Ln-1 → ...
pub uninterp spec fn reorder_list_spec(a: Seq<i64>) -> Seq<i64>;

#[verifier::external_body]
pub fn reorder_list(a: &[i64]) -> (r: Vec<i64>)
    requires a@.len() <= 100_000,
    ensures r@ == reorder_list_spec(a@),
{
    let n = a.len();
    let mut out: Vec<i64> = Vec::new();
    let mut l: usize = 0;
    let mut r: usize = if n == 0 { 0 } else { n - 1 };
    while l < r {
        out.push(a[l]);
        out.push(a[r]);
        l = l + 1;
        r = r - 1;
    }
    if l == r { out.push(a[l]); }
    out
}

// ── Implement Trie (flat-arena; result is final node count) ──
pub uninterp spec fn implement_trie_count_spec(words: Seq<Seq<u8>>) -> u64;

#[verifier::external_body]
pub fn implement_trie(words: &Vec<Vec<u8>>) -> (r: u64)
    requires
        words@.len() <= 10_000,
        forall|i: int| 0 <= i < words@.len() ==> words@[i].len() <= 100,
    ensures r == implement_trie_count_spec(Seq::<Seq<u8>>::new(words@.len(), |k: int| words@[k]@)),
{
    // Returns number of internal trie nodes created (including root).
    let mut children: Vec<[i32; 26]> = vec![[-1; 26]];
    let mut i: usize = 0;
    while i < words.len() {
        let mut node: i32 = 0;
        let w = &words[i];
        let mut j: usize = 0;
        while j < w.len() {
            let c = w[j];
            if c < b'a' || c > b'z' { break; }
            let idx = (c - b'a') as usize;
            let next = children[node as usize][idx];
            if next == -1 {
                let new_id = children.len() as i32;
                children[node as usize][idx] = new_id;
                children.push([-1; 26]);
                node = new_id;
            } else {
                node = next;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    children.len() as u64
}

// ── Add and Search Words (returns hit count over queries) ───
pub uninterp spec fn add_search_words_spec(
    words: Seq<Seq<u8>>, queries: Seq<Seq<u8>>,
) -> u64;

#[verifier::external_body]
pub fn add_search_words(words: &Vec<Vec<u8>>, queries: &Vec<Vec<u8>>) -> (r: u64)
    requires
        words@.len() <= 1_000,
        queries@.len() <= 1_000,
        forall|i: int| 0 <= i < words@.len() ==> words@[i].len() <= 50,
        forall|i: int| 0 <= i < queries@.len() ==> queries@[i].len() <= 50,
    ensures r == add_search_words_spec(
        Seq::<Seq<u8>>::new(words@.len(), |k: int| words@[k]@),
        Seq::<Seq<u8>>::new(queries@.len(), |k: int| queries@[k]@),
    ),
{
    // Linear search with '.' wildcard support.
    let mut hits: u64 = 0;
    let mut q: usize = 0;
    while q < queries.len() {
        let query = &queries[q];
        let mut found = false;
        let mut w: usize = 0;
        while w < words.len() {
            let word = &words[w];
            if word.len() == query.len() {
                let mut eq = true;
                let mut k: usize = 0;
                while k < word.len() {
                    if query[k] != b'.' && query[k] != word[k] { eq = false; break; }
                    k = k + 1;
                }
                if eq { found = true; break; }
            }
            w = w + 1;
        }
        if found { hits = hits + 1; }
        q = q + 1;
    }
    hits
}

// ── Word Search II (returns count of words found) ───────────
pub uninterp spec fn word_search_ii_count_spec(
    rows: usize, cols: usize, grid: Seq<u8>, words: Seq<Seq<u8>>,
) -> u64;

#[verifier::external_body]
pub fn word_search_ii(rows: usize, cols: usize, grid: &[u8], words: &Vec<Vec<u8>>) -> (r: u64)
    requires
        grid@.len() == rows * cols,
        rows <= 50, cols <= 50,
        words@.len() <= 100,
        forall|i: int| 0 <= i < words@.len() ==> words@[i].len() <= 20,
    ensures r == word_search_ii_count_spec(rows, cols, grid@, Seq::<Seq<u8>>::new(words@.len(), |k: int| words@[k]@)),
{
    // For each word, reuse word_search-style DFS.
    use crate::instantiations::phase4_backtracking::word_search;
    let mut count: u64 = 0;
    let mut w: usize = 0;
    while w < words.len() {
        if word_search(rows, cols, grid, &words[w]) { count = count + 1; }
        w = w + 1;
    }
    count
}

// ── Number of Islands ───────────────────────────────────────
pub uninterp spec fn number_of_islands_spec(rows: usize, cols: usize, grid: Seq<u8>) -> u64;

#[verifier::external_body]
pub fn number_of_islands(rows: usize, cols: usize, grid: &[u8]) -> (r: u64)
    requires
        grid@.len() == rows * cols,
        rows <= 500, cols <= 500,
    ensures r == number_of_islands_spec(rows, cols, grid@),
{
    fn dfs(rows: usize, cols: usize, g: &mut Vec<u8>, r: usize, c: usize) {
        if r >= rows || c >= cols { return; }
        if g[r * cols + c] != b'1' { return; }
        g.set(r * cols + c, b'0');
        if r + 1 < rows { dfs(rows, cols, g, r + 1, c); }
        if r > 0 { dfs(rows, cols, g, r - 1, c); }
        if c + 1 < cols { dfs(rows, cols, g, r, c + 1); }
        if c > 0 { dfs(rows, cols, g, r, c - 1); }
    }
    let mut g: Vec<u8> = grid.to_vec();
    let mut count: u64 = 0;
    let mut r: usize = 0;
    while r < rows {
        let mut c: usize = 0;
        while c < cols {
            if g[r * cols + c] == b'1' {
                count = count + 1;
                dfs(rows, cols, &mut g, r, c);
            }
            c = c + 1;
        }
        r = r + 1;
    }
    count
}

// ── Clone Graph (returns node count of clone) ──────────────
pub uninterp spec fn clone_graph_node_count_spec(
    n: usize, src: Seq<usize>, dst: Seq<usize>,
) -> u64;

#[verifier::external_body]
pub fn clone_graph(n: usize, src: &[usize], dst: &[usize]) -> (r: u64)
    requires
        src@.len() == dst@.len(),
        n <= 1_000,
        src@.len() <= 10_000,
    ensures r == clone_graph_node_count_spec(n, src@, dst@),
{
    // Identity clone: BFS from node 0, count reachable. Empty graph → 0.
    if n == 0 { return 0; }
    let mut visited: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < n { visited.push(false); i = i + 1; }
    let mut queue: Vec<usize> = Vec::new();
    queue.push(0); visited.set(0, true);
    let mut head: usize = 0;
    while head < queue.len() {
        let u = queue[head]; head = head + 1;
        let m = src.len();
        let mut e: usize = 0;
        while e < m {
            if src[e] == u {
                let v = dst[e];
                if v < n && !visited[v] { visited.set(v, true); queue.push(v); }
            }
            if dst[e] == u {
                let v = src[e];
                if v < n && !visited[v] { visited.set(v, true); queue.push(v); }
            }
            e = e + 1;
        }
    }
    queue.len() as u64
}

// ── Pacific Atlantic Water Flow (returns count of cells) ───
pub uninterp spec fn pacific_atlantic_count_spec(rows: usize, cols: usize, heights: Seq<i64>) -> u64;

#[verifier::external_body]
pub fn pacific_atlantic(rows: usize, cols: usize, heights: &[i64]) -> (r: u64)
    requires
        heights@.len() == rows * cols,
        rows <= 200, cols <= 200,
    ensures r == pacific_atlantic_count_spec(rows, cols, heights@),
{
    fn flow(rows: usize, cols: usize, h: &[i64], reachable: &mut Vec<bool>, r: usize, c: usize) {
        if r >= rows || c >= cols { return; }
        if reachable[r * cols + c] { return; }
        reachable.set(r * cols + c, true);
        if r + 1 < rows && h[(r + 1) * cols + c] >= h[r * cols + c] {
            flow(rows, cols, h, reachable, r + 1, c);
        }
        if r > 0 && h[(r - 1) * cols + c] >= h[r * cols + c] {
            flow(rows, cols, h, reachable, r - 1, c);
        }
        if c + 1 < cols && h[r * cols + c + 1] >= h[r * cols + c] {
            flow(rows, cols, h, reachable, r, c + 1);
        }
        if c > 0 && h[r * cols + c - 1] >= h[r * cols + c] {
            flow(rows, cols, h, reachable, r, c - 1);
        }
    }
    let mut pacific: Vec<bool> = Vec::new();
    let mut atlantic: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    let total = rows * cols;
    while i < total { pacific.push(false); atlantic.push(false); i = i + 1; }
    // Pacific from top row & left col.
    let mut c: usize = 0;
    while c < cols { flow(rows, cols, heights, &mut pacific, 0, c); c = c + 1; }
    let mut r: usize = 0;
    while r < rows { flow(rows, cols, heights, &mut pacific, r, 0); r = r + 1; }
    // Atlantic from bottom row & right col.
    let mut c: usize = 0;
    while c < cols { if rows > 0 { flow(rows, cols, heights, &mut atlantic, rows - 1, c); } c = c + 1; }
    let mut r: usize = 0;
    while r < rows { if cols > 0 { flow(rows, cols, heights, &mut atlantic, r, cols - 1); } r = r + 1; }
    let mut count: u64 = 0;
    let mut i: usize = 0;
    while i < total { if pacific[i] && atlantic[i] { count = count + 1; } i = i + 1; }
    count
}

// ── Course Schedule (topological-sort cycle detection) ─────
pub uninterp spec fn course_schedule_spec(
    n: usize, src: Seq<usize>, dst: Seq<usize>,
) -> bool;

#[verifier::external_body]
pub fn course_schedule(n: usize, src: &[usize], dst: &[usize]) -> (r: bool)
    requires
        src@.len() == dst@.len(),
        n <= 1_000,
        src@.len() <= 10_000,
    ensures r == course_schedule_spec(n, src@, dst@),
{
    // Compute in-degrees, do Kahn's algorithm. r = (#processed == n).
    let m = src.len();
    let mut indeg: Vec<u64> = Vec::new();
    let mut i: usize = 0;
    while i < n { indeg.push(0); i = i + 1; }
    let mut e: usize = 0;
    while e < m {
        let v = dst[e];
        if v < n { indeg.set(v, indeg[v] + 1); }
        e = e + 1;
    }
    let mut queue: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < n { if indeg[i] == 0 { queue.push(i); } i = i + 1; }
    let mut head: usize = 0;
    let mut processed: u64 = 0;
    while head < queue.len() {
        let u = queue[head]; head = head + 1;
        processed = processed + 1;
        let mut e: usize = 0;
        while e < m {
            if src[e] == u {
                let v = dst[e];
                if v < n && indeg[v] > 0 {
                    indeg.set(v, indeg[v] - 1);
                    if indeg[v] == 0 { queue.push(v); }
                }
            }
            e = e + 1;
        }
    }
    processed == n as u64
}

}
