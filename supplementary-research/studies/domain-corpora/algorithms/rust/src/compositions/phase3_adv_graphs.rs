//! Phase 3 — Advanced Graphs.
//!
//! Encoding contract (Rust and Python agree exactly):
//!
//! All graphs are passed as `Value::List([node_count, edge_list, ...extra])`.
//! - `node_count` : `Value::Int(n)` — nodes are `0..n`.
//! - `edge_list`  : `Value::List` of edges; each edge is
//!   `Value::List([u, v, w])` for weighted directed/undirected graphs or
//!   `Value::List([u, v])` for unweighted.
//!
//! Per-algorithm:
//!   dijkstra      : `[n, edges, src]`         → `Int(max_finite_delay)`; -1
//!                    if any node is unreachable (LeetCode 743 semantics).
//!   bellman_ford  : `[n, edges, src, dst, k]` → `Int(cheapest_cost)`; -1
//!                    if no path exists within k stops.
//!   kruskal_mst   : `[n, edges]` → `Int(mst_total_weight)`; -1 if disconnected.
//!   prim_mst      : `[n, edges]` → `Int(mst_total_weight)`; -1 if disconnected.
//!   floyd_warshall: `[n, edges]` → `List` of n×n distances (row-major Int list);
//!                    unreachable pairs represented as `Int(1<<60)`.
//!   graph_valid_tree: `[n, edges]` → `Bool`.
//!
//! Structural ordering: DAG for Dijkstra, Bellman-Ford, Prim, Floyd-Warshall;
//! Tree (sort + linear pass) for Kruskal; Linear for Graph Valid Tree. The
//! input graph may contain cycles, but the *computation's* work graph is
//! acyclic — Dijkstra's settle order (the shortest-path tree), Bellman-Ford's
//! (node, round) layers, and Prim's tree growth are all acyclic.
//!
//! All compositions are built **only** from `crate::primitives` and
//! `crate::candidates`.

use super::entry;
use crate::candidates::EquivalenceClass;
use crate::config::CorpusEntry;
use crate::equivalence::Equiv;
use crate::primitives::control::PriorityQueue;
use crate::primitives::{PropagationPass, Reduction, ResourceRegistry, Sampler};
use crate::value::Value;

const INF: i64 = 1 << 60;

// ---------------------------------------------------------------------------
// Shared decode helpers
// ---------------------------------------------------------------------------

fn decode_weighted_edges(edges: &Value) -> Vec<(usize, usize, i64)> {
    edges
        .as_list()
        .iter()
        .map(|e| {
            let t = e.as_list();
            (
                t[0].as_int() as usize,
                t[1].as_int() as usize,
                t[2].as_int(),
            )
        })
        .collect()
}

fn decode_unweighted_edges(edges: &Value) -> Vec<(usize, usize)> {
    edges
        .as_list()
        .iter()
        .map(|e| {
            let t = e.as_list();
            (t[0].as_int() as usize, t[1].as_int() as usize)
        })
        .collect()
}

fn build_adj_directed(
    n: usize,
    edges: &[(usize, usize, i64)],
) -> ResourceRegistry<usize, Vec<(usize, i64)>> {
    let mut adj: ResourceRegistry<usize, Vec<(usize, i64)>> = ResourceRegistry::new();
    for v in 0..n {
        adj.insert(v, Vec::new());
    }
    for &(u, v, w) in edges {
        adj.entry_or(u, Vec::new()).push((v, w));
    }
    adj
}

fn build_adj_undirected(
    n: usize,
    edges: &[(usize, usize, i64)],
) -> ResourceRegistry<usize, Vec<(usize, i64)>> {
    let mut adj: ResourceRegistry<usize, Vec<(usize, i64)>> = ResourceRegistry::new();
    for v in 0..n {
        adj.insert(v, Vec::new());
    }
    for &(u, v, w) in edges {
        adj.entry_or(u, Vec::new()).push((v, w));
        adj.entry_or(v, Vec::new()).push((u, w));
    }
    adj
}

// ---------------------------------------------------------------------------
// Network Delay Time — Dijkstra
//
// Composition:
//   PriorityQueue   — CompetitiveSelection-hard; extracts the unvisited node
//                     with minimum tentative distance.
//   ResourceRegistry(dist) — holds tentative distances; updated on relaxation.
//   ResourceRegistry(visited) — settled set; each node settled exactly once.
//   PropagationPass — the iterative "extract best → relax neighbours" loop
//                     is PropagationPass's fixed-point pattern bounded by n.
//   Reduction(min)  — each neighbour's new distance is min(old, via-u).
// ---------------------------------------------------------------------------

// Min-heap via negation: `(-dist, node)`.  PriorityQueue is a max-heap.
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone)]
struct DijkEntry(i64, usize);

fn dijkstra(input: Value) -> Value {
    let parts = input.as_list();
    let n = parts[0].as_int() as usize;
    let src = parts[2].as_int() as usize;
    let adj = build_adj_directed(n, &decode_weighted_edges(&parts[1]));

    // ResourceRegistry: tentative distance map.
    let mut dist: ResourceRegistry<usize, i64> = ResourceRegistry::new();
    for v in 0..n {
        dist.insert(v, INF);
    }
    dist.insert(src, 0);

    // ResourceRegistry: settled set.
    let mut visited: ResourceRegistry<usize, ()> = ResourceRegistry::new();

    // PriorityQueue (CompetitiveSelection-hard / min-heap via negation).
    let mut pq: PriorityQueue<DijkEntry> = PriorityQueue::new();
    pq.push(DijkEntry(0, src));

    // PropagationPass: iterate until the priority queue is empty (fixed point).
    // Each round extracts the best candidate (CompetitiveSelection-hard) and
    // relaxes its outgoing edges (Reduction-min per neighbour).
    while let Some(DijkEntry(neg_d, u)) = pq.pop_best() {
        let d = -neg_d;
        if visited.contains(&u) {
            continue;
        }
        visited.insert(u, ());
        for &(v, w) in adj.lookup(&u).unwrap_or(&Vec::new()) {
            let cur = *dist.lookup(&v).unwrap_or(&INF);
            // Reduction(min) over {current dist, dist-via-u}.
            let via: i64 = Reduction::reduce([cur, d + w], INF, |a: i64, b: i64| a.min(b));
            if via < cur {
                dist.insert(v, via);
                pq.push(DijkEntry(-via, v));
            }
        }
    }

    // LeetCode 743: return max delay; -1 if any node is unreachable.
    let max_d = Reduction::reduce(
        (0..n).map(|v| *dist.lookup(&v).unwrap_or(&INF)),
        0i64,
        |a, b| a.max(b),
    );
    Value::Int(if max_d >= INF { -1 } else { max_d })
}

// ---------------------------------------------------------------------------
// Cheapest Flights Within K Stops — Bellman-Ford
//
// Composition:
//   PropagationPass — K+1 rounds of all-edge relaxation: round-based
//                     propagation toward a fixed point.
//   Reduction(min)  — each target vertex's distance is min(prev, via-edge).
//
// The snapshot trick (copy `dist` before each round) enforces the "at most
// K intermediate stops" invariant: intra-round updates are not visible to
// sibling relaxations in the same round.
// ---------------------------------------------------------------------------

fn bellman_ford(input: Value) -> Value {
    let parts = input.as_list();
    let n = parts[0].as_int() as usize;
    let edges = decode_weighted_edges(&parts[1]);
    let src = parts[2].as_int() as usize;
    let dst = parts[3].as_int() as usize;
    let k = parts[4].as_int() as usize; // max intermediate stops

    // Initial distance state: 0 at src, INF elsewhere.
    let init: Vec<i64> = (0..n).map(|v| if v == src { 0 } else { INF }).collect();

    // PropagationPass: K+1 rounds (K stops = K+1 edges traversed).
    let final_dist = PropagationPass::run(
        init,
        |dist: &Vec<i64>| {
            let prev = dist.clone(); // snapshot — Bellman-Ford round isolation
            let mut next = dist.clone();
            for &(u, v, w) in &edges {
                if prev[u] < INF {
                    // Reduction(min): new dist[v] = min(current, dist[u]+w).
                    next[v] =
                        Reduction::reduce([next[v], prev[u] + w], INF, |a: i64, b: i64| a.min(b));
                }
            }
            next
        },
        k + 1,
    );

    let d = final_dist[dst];
    Value::Int(if d >= INF { -1 } else { d })
}

// ---------------------------------------------------------------------------
// Minimum Spanning Tree — Kruskal
//
// Composition:
//   EquivalenceClass — union-find for cycle detection and component merge.
//
// Structural ordering: Tree — sort (independent of linear pass) followed by
// a linear scan. The sort is a domain-level operation; the structural work
// is the linear pass under EquivalenceClass.
// ---------------------------------------------------------------------------

fn kruskal_mst(input: Value) -> Value {
    let parts = input.as_list();
    let n = parts[0].as_int() as usize;
    let mut edges = decode_weighted_edges(&parts[1]);

    if n == 0 {
        return Value::Int(0);
    }

    // Sort edges by weight (domain sort — not a catalog primitive).
    edges.sort_by_key(|&(_, _, w)| w);

    let mut uf = EquivalenceClass::new(n);
    let mut total_w = 0i64;
    let mut edge_count = 0usize;

    // Linear pass: for each edge, union its endpoints; accept iff they were
    // in different components (EquivalenceClass::union returns false on cycle).
    for (u, v, w) in edges {
        if uf.union(u, v) {
            total_w += w;
            edge_count += 1;
            if edge_count == n - 1 {
                break;
            }
        }
    }

    // MST exists iff exactly n-1 edges were accepted (connected graph).
    Value::Int(if edge_count + 1 == n { total_w } else { -1 })
}

// ---------------------------------------------------------------------------
// Minimum Spanning Tree — Prim
//
// Composition:
//   PriorityQueue   — CompetitiveSelection-hard; extracts the cheapest
//                     crossing edge at each step.
//   ResourceRegistry(in_tree) — tracks which vertices are in the growing tree.
//   PropagationPass — each addition of a new vertex expands the candidate
//                     edge set (the cut), analogous to relaxation in Dijkstra.
//   Reduction(sum)  — accumulate total MST weight.
// ---------------------------------------------------------------------------

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone)]
struct PrimEntry(i64, usize); // (-weight, node) for min-heap via negation

fn prim_mst(input: Value) -> Value {
    let parts = input.as_list();
    let n = parts[0].as_int() as usize;
    let edges = decode_weighted_edges(&parts[1]);

    if n == 0 {
        return Value::Int(0);
    }

    let adj = build_adj_undirected(n, &edges);

    // ResourceRegistry: in-tree vertex set.
    let mut in_tree: ResourceRegistry<usize, ()> = ResourceRegistry::new();
    in_tree.insert(0, ());

    // PriorityQueue (CompetitiveSelection-hard / min-heap via negation).
    let mut pq: PriorityQueue<PrimEntry> = PriorityQueue::new();
    for &(v, w) in adj.lookup(&0).unwrap_or(&Vec::new()) {
        pq.push(PrimEntry(-w, v));
    }

    let mut total_w = 0i64;
    let mut in_count = 1usize;

    // PropagationPass: extract cheapest crossing edge, add vertex to tree,
    // expand cut with new vertex's edges.
    while let Some(PrimEntry(neg_w, u)) = pq.pop_best() {
        if in_tree.contains(&u) {
            continue;
        }
        let w = -neg_w;
        in_tree.insert(u, ());
        // Reduction(sum): accumulate MST weight.
        total_w = Reduction::reduce([total_w, w], 0i64, |a, b| a + b);
        in_count += 1;
        for &(v, wv) in adj.lookup(&u).unwrap_or(&Vec::new()) {
            if !in_tree.contains(&v) {
                pq.push(PrimEntry(-wv, v));
            }
        }
    }

    Value::Int(if in_count == n { total_w } else { -1 })
}

// ---------------------------------------------------------------------------
// Floyd-Warshall — all-pairs shortest paths
//
// Composition:
//   ResourceRegistry — 2D distance matrix indexed by `(i, j)`.
//   Reduction(min)  — each cell updated as min(dist[i][j], dist[i][k]+dist[k][j]).
//
// Structural ordering: DAG — the three nested loops form a 3-D dependency
// where each k-stage depends only on the completed (k-1)-stage.
// ---------------------------------------------------------------------------

fn floyd_warshall(input: Value) -> Value {
    let parts = input.as_list();
    let n = parts[0].as_int() as usize;
    let edges = decode_weighted_edges(&parts[1]);

    // ResourceRegistry: 2D distance matrix.
    let mut dist: ResourceRegistry<(usize, usize), i64> = ResourceRegistry::new();
    for i in 0..n {
        for j in 0..n {
            dist.insert((i, j), if i == j { 0 } else { INF });
        }
    }
    // Populate from edge list; keep minimum over parallel edges.
    for &(u, v, w) in &edges {
        let cur = *dist.lookup(&(u, v)).unwrap_or(&INF);
        dist.insert(
            (u, v),
            Reduction::reduce([cur, w], INF, |a: i64, b: i64| a.min(b)),
        );
    }

    // Triple loop: for each intermediate vertex k update all (i,j) pairs.
    for k in 0..n {
        for i in 0..n {
            for j in 0..n {
                let cur = *dist.lookup(&(i, j)).unwrap_or(&INF);
                let ik = *dist.lookup(&(i, k)).unwrap_or(&INF);
                let kj = *dist.lookup(&(k, j)).unwrap_or(&INF);
                let via = if ik >= INF || kj >= INF { INF } else { ik + kj };
                // Reduction(min) over {direct, via-k}.
                let updated = Reduction::reduce([cur, via], INF, |a: i64, b: i64| a.min(b));
                dist.insert((i, j), updated);
            }
        }
    }

    // Emit row-major flat list.
    let flat: Vec<Value> = (0..n)
        .flat_map(|i| (0..n).map(move |j| (i, j)))
        .map(|(i, j)| Value::Int(*dist.lookup(&(i, j)).unwrap_or(&INF)))
        .collect();
    Value::List(flat)
}

// ---------------------------------------------------------------------------
// Graph Valid Tree
//
// Composition:
//   EquivalenceClass — union-find for cycle detection and connectivity check.
//
// A valid tree on n nodes has exactly n-1 edges, is acyclic, and is connected.
// EquivalenceClass's `union` returns false on a duplicate-class attempt (cycle).
// After all unions, class_count() == 1 proves connectivity.
// ---------------------------------------------------------------------------

fn graph_valid_tree(input: Value) -> Value {
    let parts = input.as_list();
    let n = parts[0].as_int() as usize;
    let edges = decode_unweighted_edges(&parts[1]);

    if n == 0 {
        return Value::Bool(true);
    }
    // Necessary condition: exactly n-1 edges.
    if edges.len() != n - 1 {
        return Value::Bool(false);
    }

    let mut uf = EquivalenceClass::new(n);
    for (u, v) in edges {
        if !uf.union(u, v) {
            return Value::Bool(false); // cycle detected
        }
    }
    // Connected iff exactly one class remains.
    Value::Bool(uf.class_count() == 1)
}

// ---------------------------------------------------------------------------
// Input generators — curated edge cases + ~1000 property inputs
// ---------------------------------------------------------------------------

/// Build a random connected weighted directed graph, returned as a Vec<Value>
/// of `[u, v, w]` triples, with `n` nodes (guaranteed-connected via a chain).
fn rand_directed_edges(s: &mut Sampler, n: usize, w_max: i64) -> Vec<Value> {
    let mut edges: Vec<Value> = Vec::new();
    // Chain 0 → 1 → 2 → … → n-1 guarantees reachability from 0.
    for i in 0..n - 1 {
        let w = 1 + s.pick_index(w_max as usize) as i64;
        edges.push(Value::List(vec![
            Value::Int(i as i64),
            Value::Int((i + 1) as i64),
            Value::Int(w),
        ]));
    }
    let extra = s.pick_index(n + 2);
    for _ in 0..extra {
        let u = s.pick_index(n);
        let v = s.pick_index(n);
        let w = 1 + s.pick_index(w_max as usize) as i64;
        edges.push(Value::List(vec![
            Value::Int(u as i64),
            Value::Int(v as i64),
            Value::Int(w),
        ]));
    }
    edges
}

/// Build a random connected weighted undirected graph.
fn rand_undirected_edges(s: &mut Sampler, n: usize, w_max: i64) -> Vec<Value> {
    let mut edges: Vec<Value> = Vec::new();
    // Spanning chain for connectivity.
    for i in 0..n - 1 {
        let w = 1 + s.pick_index(w_max as usize) as i64;
        edges.push(Value::List(vec![
            Value::Int(i as i64),
            Value::Int((i + 1) as i64),
            Value::Int(w),
        ]));
    }
    let extra = s.pick_index(n + 2);
    for _ in 0..extra {
        let u = s.pick_index(n);
        let v = (u + 1 + s.pick_index(n.saturating_sub(1).max(1))) % n;
        let w = 1 + s.pick_index(w_max as usize) as i64;
        edges.push(Value::List(vec![
            Value::Int(u as i64),
            Value::Int(v as i64),
            Value::Int(w),
        ]));
    }
    edges
}

// --- Dijkstra generator ---
fn g_dijkstra() -> Vec<Value> {
    // Curated: LeetCode 743 example adapted to 0-indexed nodes.
    // Original: n=4, edges [[2,1,1],[2,3,1],[3,4,1]], src=2 (1-indexed).
    // 0-indexed: n=4, edges [[1,0,1],[1,2,1],[2,3,1]], src=1.
    let mut v = vec![
        Value::List(vec![
            Value::Int(4),
            Value::List(vec![
                Value::List(vec![Value::Int(1), Value::Int(0), Value::Int(1)]),
                Value::List(vec![Value::Int(1), Value::Int(2), Value::Int(1)]),
                Value::List(vec![Value::Int(2), Value::Int(3), Value::Int(1)]),
            ]),
            Value::Int(1),
        ]),
        // n=1, src=0.
        Value::List(vec![Value::Int(1), Value::List(vec![]), Value::Int(0)]),
        // n=2, no edges — node 1 unreachable from 0.
        Value::List(vec![Value::Int(2), Value::List(vec![]), Value::Int(0)]),
        // n=2, edge 0→1 w=7.
        Value::List(vec![
            Value::Int(2),
            Value::List(vec![Value::List(vec![
                Value::Int(0),
                Value::Int(1),
                Value::Int(7),
            ])]),
            Value::Int(0),
        ]),
    ];
    let mut s = Sampler::new(50);
    for _ in 0..1000 {
        let n = 2 + s.pick_index(6); // 2..=7
        let edges = rand_directed_edges(&mut s, n, 10);
        let src = s.pick_index(n);
        v.push(Value::List(vec![
            Value::Int(n as i64),
            Value::List(edges),
            Value::Int(src as i64),
        ]));
    }
    v
}

// --- Bellman-Ford generator ---
fn g_bellman_ford() -> Vec<Value> {
    let mut v = vec![
        // LeetCode 787 example: 3 nodes, k=1 stop.
        Value::List(vec![
            Value::Int(3),
            Value::List(vec![
                Value::List(vec![Value::Int(0), Value::Int(1), Value::Int(100)]),
                Value::List(vec![Value::Int(1), Value::Int(2), Value::Int(100)]),
                Value::List(vec![Value::Int(0), Value::Int(2), Value::Int(500)]),
            ]),
            Value::Int(0),
            Value::Int(2),
            Value::Int(1),
        ]),
        // No path: only 0→1 edge, dst=2.
        Value::List(vec![
            Value::Int(3),
            Value::List(vec![Value::List(vec![
                Value::Int(0),
                Value::Int(1),
                Value::Int(10),
            ])]),
            Value::Int(0),
            Value::Int(2),
            Value::Int(2),
        ]),
        // k=0: direct edge exists.
        Value::List(vec![
            Value::Int(3),
            Value::List(vec![Value::List(vec![
                Value::Int(0),
                Value::Int(2),
                Value::Int(7),
            ])]),
            Value::Int(0),
            Value::Int(2),
            Value::Int(0),
        ]),
    ];
    let mut s = Sampler::new(51);
    for _ in 0..1000 {
        let n = 2 + s.pick_index(5); // 2..=6
        let edges = rand_directed_edges(&mut s, n, 20);
        let src = s.pick_index(n);
        let dst = s.pick_index(n);
        let k = s.pick_index(n + 2);
        v.push(Value::List(vec![
            Value::Int(n as i64),
            Value::List(edges),
            Value::Int(src as i64),
            Value::Int(dst as i64),
            Value::Int(k as i64),
        ]));
    }
    v
}

// --- Kruskal generator ---
fn g_kruskal() -> Vec<Value> {
    let mut v = vec![
        // Triangle.
        Value::List(vec![
            Value::Int(3),
            Value::List(vec![
                Value::List(vec![Value::Int(0), Value::Int(1), Value::Int(1)]),
                Value::List(vec![Value::Int(1), Value::Int(2), Value::Int(2)]),
                Value::List(vec![Value::Int(0), Value::Int(2), Value::Int(3)]),
            ]),
        ]),
        // Single node.
        Value::List(vec![Value::Int(1), Value::List(vec![])]),
        // Two nodes, one edge.
        Value::List(vec![
            Value::Int(2),
            Value::List(vec![Value::List(vec![
                Value::Int(0),
                Value::Int(1),
                Value::Int(5),
            ])]),
        ]),
        // Disconnected — MST impossible.
        Value::List(vec![
            Value::Int(3),
            Value::List(vec![Value::List(vec![
                Value::Int(0),
                Value::Int(1),
                Value::Int(1),
            ])]),
        ]),
    ];
    let mut s = Sampler::new(52);
    for _ in 0..1000 {
        let n = 2 + s.pick_index(6); // 2..=7
        let edges = rand_undirected_edges(&mut s, n, 15);
        v.push(Value::List(vec![Value::Int(n as i64), Value::List(edges)]));
    }
    v
}

// --- Prim generator ---
fn g_prim() -> Vec<Value> {
    let mut v = vec![
        // Triangle.
        Value::List(vec![
            Value::Int(3),
            Value::List(vec![
                Value::List(vec![Value::Int(0), Value::Int(1), Value::Int(1)]),
                Value::List(vec![Value::Int(1), Value::Int(2), Value::Int(2)]),
                Value::List(vec![Value::Int(0), Value::Int(2), Value::Int(3)]),
            ]),
        ]),
        // Single node.
        Value::List(vec![Value::Int(1), Value::List(vec![])]),
        // Two nodes, one edge.
        Value::List(vec![
            Value::Int(2),
            Value::List(vec![Value::List(vec![
                Value::Int(0),
                Value::Int(1),
                Value::Int(5),
            ])]),
        ]),
        // Disconnected — MST impossible.
        Value::List(vec![
            Value::Int(3),
            Value::List(vec![Value::List(vec![
                Value::Int(0),
                Value::Int(1),
                Value::Int(1),
            ])]),
        ]),
    ];
    let mut s = Sampler::new(53);
    for _ in 0..1000 {
        let n = 2 + s.pick_index(6);
        let edges = rand_undirected_edges(&mut s, n, 15);
        v.push(Value::List(vec![Value::Int(n as i64), Value::List(edges)]));
    }
    v
}

// --- Floyd-Warshall generator ---
fn g_floyd_warshall() -> Vec<Value> {
    let mut v = vec![
        // 3-node directed.
        Value::List(vec![
            Value::Int(3),
            Value::List(vec![
                Value::List(vec![Value::Int(0), Value::Int(1), Value::Int(3)]),
                Value::List(vec![Value::Int(1), Value::Int(2), Value::Int(2)]),
                Value::List(vec![Value::Int(0), Value::Int(2), Value::Int(8)]),
                Value::List(vec![Value::Int(2), Value::Int(0), Value::Int(5)]),
            ]),
        ]),
        // Single node.
        Value::List(vec![Value::Int(1), Value::List(vec![])]),
        // No edges.
        Value::List(vec![Value::Int(2), Value::List(vec![])]),
        // Dense 4-node.
        Value::List(vec![
            Value::Int(4),
            Value::List(vec![
                Value::List(vec![Value::Int(0), Value::Int(1), Value::Int(1)]),
                Value::List(vec![Value::Int(1), Value::Int(2), Value::Int(1)]),
                Value::List(vec![Value::Int(2), Value::Int(3), Value::Int(1)]),
                Value::List(vec![Value::Int(3), Value::Int(0), Value::Int(1)]),
                Value::List(vec![Value::Int(0), Value::Int(2), Value::Int(5)]),
            ]),
        ]),
    ];
    // Keep n ≤ 4 so the n*n output list stays compact.
    let mut s = Sampler::new(54);
    for _ in 0..1000 {
        let n = 2 + s.pick_index(3); // 2..=4
        let m = s.pick_index(n * 2 + 1);
        let edges: Vec<Value> = (0..m)
            .map(|_| {
                let u = s.pick_index(n);
                let v = s.pick_index(n);
                let w = 1 + s.pick_index(10) as i64;
                Value::List(vec![
                    Value::Int(u as i64),
                    Value::Int(v as i64),
                    Value::Int(w),
                ])
            })
            .collect();
        v.push(Value::List(vec![Value::Int(n as i64), Value::List(edges)]));
    }
    v
}

// --- Graph Valid Tree generator ---
fn g_graph_valid_tree() -> Vec<Value> {
    let mut v = vec![
        // LeetCode 261 example 1 → true.
        Value::List(vec![
            Value::Int(5),
            Value::List(vec![
                Value::List(vec![Value::Int(0), Value::Int(1)]),
                Value::List(vec![Value::Int(0), Value::Int(2)]),
                Value::List(vec![Value::Int(0), Value::Int(3)]),
                Value::List(vec![Value::Int(1), Value::Int(4)]),
            ]),
        ]),
        // LeetCode 261 example 2 → false (cycle).
        Value::List(vec![
            Value::Int(5),
            Value::List(vec![
                Value::List(vec![Value::Int(0), Value::Int(1)]),
                Value::List(vec![Value::Int(1), Value::Int(2)]),
                Value::List(vec![Value::Int(2), Value::Int(3)]),
                Value::List(vec![Value::Int(1), Value::Int(3)]),
                Value::List(vec![Value::Int(1), Value::Int(4)]),
            ]),
        ]),
        // Single node → true.
        Value::List(vec![Value::Int(1), Value::List(vec![])]),
        // Two nodes, one edge → true.
        Value::List(vec![
            Value::Int(2),
            Value::List(vec![Value::List(vec![Value::Int(0), Value::Int(1)])]),
        ]),
        // Two nodes, no edges → false (disconnected).
        Value::List(vec![Value::Int(2), Value::List(vec![])]),
        // Path 0-1-2 → true.
        Value::List(vec![
            Value::Int(3),
            Value::List(vec![
                Value::List(vec![Value::Int(0), Value::Int(1)]),
                Value::List(vec![Value::Int(1), Value::Int(2)]),
            ]),
        ]),
    ];
    let mut s = Sampler::new(55);
    for _ in 0..1000 {
        let n = 1 + s.pick_index(7); // 1..=7
        let make_tree = s.pick_index(2) == 0;
        let edges: Vec<Value> = if make_tree && n > 1 {
            // Valid spanning tree: random parent for each node i in [1,n).
            (1..n)
                .map(|i| {
                    let parent = s.pick_index(i);
                    Value::List(vec![Value::Int(parent as i64), Value::Int(i as i64)])
                })
                .collect()
        } else {
            let m = s.pick_index(n + 1);
            (0..m)
                .map(|_| {
                    let u = s.pick_index(n);
                    let v = s.pick_index(n);
                    Value::List(vec![Value::Int(u as i64), Value::Int(v as i64)])
                })
                .collect()
        };
        v.push(Value::List(vec![Value::Int(n as i64), Value::List(edges)]));
    }
    v
}

// ---------------------------------------------------------------------------
// Registry
// ---------------------------------------------------------------------------

pub fn add(r: &mut Vec<CorpusEntry>) {
    let dijk = "PriorityQueue(CompetitiveSelection-hard) + ResourceRegistry(dist/visited) + PropagationPass + Reduction(min)";
    let bf = "PropagationPass(K+1 rounds) + Reduction(min)";
    let krus = "EquivalenceClass(union-find)";
    let prim = "PriorityQueue(CompetitiveSelection-hard) + ResourceRegistry(in-tree) + PropagationPass + Reduction(sum)";
    let fw = "ResourceRegistry(dist matrix) + Reduction(min)";
    let gvt = "EquivalenceClass(union-find)";

    entry(
        r,
        "Network Delay Time",
        "Advanced Graphs",
        3,
        "DAG",
        dijk,
        dijkstra,
        "dijkstra",
        Equiv::Exact,
        g_dijkstra,
    );
    entry(
        r,
        "Cheapest Flights Within K Stops",
        "Advanced Graphs",
        3,
        "DAG",
        bf,
        bellman_ford,
        "bellman_ford",
        Equiv::Exact,
        g_bellman_ford,
    );
    entry(
        r,
        "Minimum Spanning Tree (Kruskal)",
        "Advanced Graphs",
        3,
        "Tree",
        krus,
        kruskal_mst,
        "kruskal_mst",
        Equiv::Exact,
        g_kruskal,
    );
    entry(
        r,
        "Minimum Spanning Tree (Prim)",
        "Advanced Graphs",
        3,
        "DAG",
        prim,
        prim_mst,
        "prim_mst",
        Equiv::Exact,
        g_prim,
    );
    entry(
        r,
        "Floyd-Warshall",
        "Advanced Graphs",
        3,
        "DAG",
        fw,
        floyd_warshall,
        "floyd_warshall",
        Equiv::Exact,
        g_floyd_warshall,
    );
    entry(
        r,
        "Graph Valid Tree",
        "Advanced Graphs",
        3,
        "Linear",
        gvt,
        graph_valid_tree,
        "graph_valid_tree",
        Equiv::BoolEq,
        g_graph_valid_tree,
    );
}
