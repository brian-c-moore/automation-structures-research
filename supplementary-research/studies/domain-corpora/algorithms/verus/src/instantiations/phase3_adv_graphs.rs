// Advanced graph algorithms.
//
// Six algorithms vendored from supplementary-research/studies/domain-corpora/algorithms/rust/src/compositions/
// phase3_adv_graphs.rs. Each is a PriorityDrivenPropagation
// (Dijkstra, Prim) or a relaxation/MST/closure variant. Edge lists
// are represented as three parallel slices (src, dst, weight).

use vstd::prelude::*;

verus! {

// ── Dijkstra (single-source shortest paths) ─────────────────
pub uninterp spec fn dijkstra_spec(
    n: usize, src: Seq<usize>, dst: Seq<usize>, w: Seq<i64>, source: usize,
) -> Seq<i64>;

const INF_DIST: i64 = 1i64 << 60;

#[verifier::external_body]
pub fn dijkstra(n: usize, src: &[usize], dst: &[usize], w: &[i64], source: usize) -> (r: Vec<i64>)
    requires
        src@.len() == dst@.len(),
        src@.len() == w@.len(),
        n <= 1_000,
        src@.len() <= 10_000,
        source < n,
    ensures r@ == dijkstra_spec(n, src@, dst@, w@, source),
{
    let mut dist: Vec<i64> = Vec::new();
    let mut visited: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        dist.push(INF_DIST);
        visited.push(false);
        i = i + 1;
    }
    dist.set(source, 0);
    let mut iter: usize = 0;
    while iter < n {
        // Extract min over non-visited dist (Bisection role via linear scan).
        let mut u: usize = n;
        let mut best: i64 = INF_DIST;
        let mut i: usize = 0;
        while i < n {
            if !visited[i] && dist[i] < best { best = dist[i]; u = i; }
            i = i + 1;
        }
        if u == n { break; }
        visited.set(u, true);
        // Relax outgoing edges.
        let m = src.len();
        let mut e: usize = 0;
        while e < m {
            if src[e] == u {
                let v = dst[e];
                let wt = w[e];
                if v < n && dist[u] != INF_DIST {
                    let cand = dist[u] + wt;
                    if cand < dist[v] { dist.set(v, cand); }
                }
            }
            e = e + 1;
        }
        iter = iter + 1;
    }
    dist
}

// ── Bellman-Ford (single-source SP with negative weights) ──
pub uninterp spec fn bellman_ford_spec(
    n: usize, src: Seq<usize>, dst: Seq<usize>, w: Seq<i64>, source: usize,
) -> Seq<i64>;

#[verifier::external_body]
pub fn bellman_ford(n: usize, src: &[usize], dst: &[usize], w: &[i64], source: usize) -> (r: Vec<i64>)
    requires
        src@.len() == dst@.len(),
        src@.len() == w@.len(),
        n <= 1_000,
        src@.len() <= 10_000,
        source < n,
    ensures r@ == bellman_ford_spec(n, src@, dst@, w@, source),
{
    let mut dist: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n { dist.push(INF_DIST); i = i + 1; }
    dist.set(source, 0);
    let m = src.len();
    let mut iter: usize = 0;
    while iter + 1 < n {
        let mut e: usize = 0;
        while e < m {
            let u = src[e];
            let v = dst[e];
            let wt = w[e];
            if u < n && v < n && dist[u] != INF_DIST {
                let cand = dist[u] + wt;
                if cand < dist[v] { dist.set(v, cand); }
            }
            e = e + 1;
        }
        iter = iter + 1;
    }
    dist
}

// ── Kruskal MST (union-find via array) ──────────────────────
// Returns total weight of MST. -1 if disconnected.
pub uninterp spec fn kruskal_spec(
    n: usize, src: Seq<usize>, dst: Seq<usize>, w: Seq<i64>,
) -> i64;

#[verifier::external_body]
pub fn kruskal_mst(n: usize, src: &[usize], dst: &[usize], w: &[i64]) -> (r: i64)
    requires
        src@.len() == dst@.len(),
        src@.len() == w@.len(),
        n <= 1_000,
        src@.len() <= 10_000,
    ensures r == kruskal_spec(n, src@, dst@, w@),
{
    // Sort edges by weight via simple indices + selection sort.
    let m = src.len();
    let mut order: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < m { order.push(i); i = i + 1; }
    let mut i: usize = 0;
    while i < m {
        let mut best: usize = i;
        let mut j: usize = i + 1;
        while j < m {
            if w[order[j]] < w[order[best]] { best = j; }
            j = j + 1;
        }
        let t = order[i]; order.set(i, order[best]); order.set(best, t);
        i = i + 1;
    }
    // Union-find.
    let mut parent: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < n { parent.push(i); i = i + 1; }
    let mut total: i64 = 0;
    let mut edges_taken: usize = 0;
    let mut k: usize = 0;
    while k < m {
        let e = order[k];
        let u = src[e]; let v = dst[e];
        if u < n && v < n {
            // Find root with path-walking (no compression for verification simplicity).
            let mut ru = u;
            while parent[ru] != ru { ru = parent[ru]; }
            let mut rv = v;
            while parent[rv] != rv { rv = parent[rv]; }
            if ru != rv {
                parent.set(ru, rv);
                total = total + w[e];
                edges_taken = edges_taken + 1;
                if edges_taken + 1 == n { return total; }
            }
        }
        k = k + 1;
    }
    if edges_taken + 1 < n { return -1; }
    total
}

// ── Prim MST ─────────────────────────────────────────────────
pub uninterp spec fn prim_spec(
    n: usize, src: Seq<usize>, dst: Seq<usize>, w: Seq<i64>,
) -> i64;

#[verifier::external_body]
pub fn prim_mst(n: usize, src: &[usize], dst: &[usize], w: &[i64]) -> (r: i64)
    requires
        src@.len() == dst@.len(),
        src@.len() == w@.len(),
        n <= 1_000,
        src@.len() <= 10_000,
    ensures r == prim_spec(n, src@, dst@, w@),
{
    if n == 0 { return 0; }
    let mut in_tree: Vec<bool> = Vec::new();
    let mut min_edge: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n { in_tree.push(false); min_edge.push(INF_DIST); i = i + 1; }
    min_edge.set(0, 0);
    let mut total: i64 = 0;
    let mut iter: usize = 0;
    while iter < n {
        let mut u: usize = n;
        let mut best: i64 = INF_DIST;
        let mut i: usize = 0;
        while i < n {
            if !in_tree[i] && min_edge[i] < best { best = min_edge[i]; u = i; }
            i = i + 1;
        }
        if u == n { return -1; }
        in_tree.set(u, true);
        total = total + min_edge[u];
        let m = src.len();
        let mut e: usize = 0;
        while e < m {
            let a = src[e]; let b = dst[e]; let wt = w[e];
            if a == u && b < n && !in_tree[b] && wt < min_edge[b] { min_edge.set(b, wt); }
            if b == u && a < n && !in_tree[a] && wt < min_edge[a] { min_edge.set(a, wt); }
            e = e + 1;
        }
        iter = iter + 1;
    }
    total
}

// ── Floyd-Warshall (all-pairs shortest paths) ───────────────
// Returns flat (n×n) Vec<i64> of pairwise distances.
pub uninterp spec fn floyd_warshall_spec(
    n: usize, src: Seq<usize>, dst: Seq<usize>, w: Seq<i64>,
) -> Seq<i64>;

#[verifier::external_body]
pub fn floyd_warshall(n: usize, src: &[usize], dst: &[usize], w: &[i64]) -> (r: Vec<i64>)
    requires
        src@.len() == dst@.len(),
        src@.len() == w@.len(),
        n <= 100,
        src@.len() <= 1_000,
    ensures r@ == floyd_warshall_spec(n, src@, dst@, w@),
{
    let total: usize = n * n;
    let mut dist: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < total { dist.push(INF_DIST); k = k + 1; }
    let mut i: usize = 0;
    while i < n { dist.set(i * n + i, 0); i = i + 1; }
    let m = src.len();
    let mut e: usize = 0;
    while e < m {
        let u = src[e]; let v = dst[e]; let wt = w[e];
        if u < n && v < n {
            let idx = u * n + v;
            if wt < dist[idx] { dist.set(idx, wt); }
        }
        e = e + 1;
    }
    let mut k: usize = 0;
    while k < n {
        let mut i: usize = 0;
        while i < n {
            let mut j: usize = 0;
            while j < n {
                let ij = i * n + j;
                let ik = i * n + k;
                let kj = k * n + j;
                if dist[ik] != INF_DIST && dist[kj] != INF_DIST {
                    let cand = dist[ik] + dist[kj];
                    if cand < dist[ij] { dist.set(ij, cand); }
                }
                j = j + 1;
            }
            i = i + 1;
        }
        k = k + 1;
    }
    dist
}

// ── Graph Valid Tree (connectivity + acyclicity) ────────────
pub uninterp spec fn graph_valid_tree_spec(
    n: usize, src: Seq<usize>, dst: Seq<usize>,
) -> bool;

#[verifier::external_body]
pub fn graph_valid_tree(n: usize, src: &[usize], dst: &[usize]) -> (r: bool)
    requires
        src@.len() == dst@.len(),
        n <= 1_000,
        src@.len() <= 10_000,
    ensures r == graph_valid_tree_spec(n, src@, dst@),
{
    // n nodes form a tree iff |edges| == n-1 AND connected (no cycle).
    let m = src.len();
    if n == 0 { return true; }
    if m + 1 != n { return false; }
    // Union-find: detect cycles.
    let mut parent: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < n { parent.push(i); i = i + 1; }
    let mut e: usize = 0;
    while e < m {
        let u = src[e]; let v = dst[e];
        if u >= n || v >= n { return false; }
        let mut ru = u;
        while parent[ru] != ru { ru = parent[ru]; }
        let mut rv = v;
        while parent[rv] != rv { rv = parent[rv]; }
        if ru == rv { return false; }
        parent.set(ru, rv);
        e = e + 1;
    }
    true
}

}
