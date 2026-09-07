"""Phase 3 — Advanced Graphs: idiomatic Python reference oracles.

Independent of the Rust primitive implementations under test.
Each oracle is the classic textbook formulation. Exposes ORACLES (name -> fn).

Encoding contract (matches Rust exactly):
  All graphs: [node_count, edge_list, ...extra]
    node_count : int  (nodes are 0-indexed, 0..n)
    edge_list  : list of edges; weighted edge = [u, v, w]; unweighted = [u, v]

  dijkstra      : [n, edges, src]          -> int (max delay or -1)
  bellman_ford  : [n, edges, src, dst, k]  -> int (cheapest or -1)
  kruskal_mst   : [n, edges]               -> int (mst weight or -1)
  prim_mst      : [n, edges]               -> int (mst weight or -1)
  floyd_warshall: [n, edges]               -> list[int] (n*n row-major distances)
  graph_valid_tree: [n, edges]             -> bool
"""

import heapq

INF = 1 << 60


# ---------------------------------------------------------------------------
# Network Delay Time — Dijkstra
# LeetCode 743 semantics: return max dist over all nodes, or -1 if any
# node is unreachable from src.
# ---------------------------------------------------------------------------

def dijkstra(args):
    n, edges, src = args[0], args[1], args[2]
    # Build adjacency list (directed).
    adj = [[] for _ in range(n)]
    for e in edges:
        u, v, w = e[0], e[1], e[2]
        adj[u].append((v, w))

    dist = [INF] * n
    dist[src] = 0
    heap = [(0, src)]  # (dist, node)

    while heap:
        d, u = heapq.heappop(heap)
        if d > dist[u]:
            continue
        for v, w in adj[u]:
            nd = d + w
            if nd < dist[v]:
                dist[v] = nd
                heapq.heappush(heap, (nd, v))

    max_d = max(dist)
    return -1 if max_d >= INF else max_d


# ---------------------------------------------------------------------------
# Cheapest Flights Within K Stops — Bellman-Ford
# LeetCode 787: k stops = k+1 edges.
# ---------------------------------------------------------------------------

def bellman_ford(args):
    n, edges, src, dst, k = args[0], args[1], args[2], args[3], args[4]

    dist = [INF] * n
    dist[src] = 0

    for _ in range(k + 1):
        prev = dist[:]
        for e in edges:
            u, v, w = e[0], e[1], e[2]
            if prev[u] < INF:
                candidate = prev[u] + w
                if candidate < dist[v]:
                    dist[v] = candidate

    return -1 if dist[dst] >= INF else dist[dst]


# ---------------------------------------------------------------------------
# Minimum Spanning Tree — Kruskal
# Returns total MST weight, or -1 if the graph is disconnected.
# ---------------------------------------------------------------------------

def _find(parent, x):
    while parent[x] != x:
        parent[x] = parent[parent[x]]  # path compression
        x = parent[x]
    return x


def _union(parent, rank, x, y):
    rx, ry = _find(parent, x), _find(parent, y)
    if rx == ry:
        return False
    if rank[rx] < rank[ry]:
        rx, ry = ry, rx
    parent[ry] = rx
    if rank[rx] == rank[ry]:
        rank[rx] += 1
    return True


def kruskal_mst(args):
    n, edges = args[0], args[1]
    if n == 0:
        return 0
    sorted_edges = sorted(edges, key=lambda e: e[2])
    parent = list(range(n))
    rank = [0] * n
    total_w = 0
    count = 0
    for e in sorted_edges:
        u, v, w = e[0], e[1], e[2]
        if _union(parent, rank, u, v):
            total_w += w
            count += 1
            if count == n - 1:
                break
    return total_w if count == n - 1 else -1


# ---------------------------------------------------------------------------
# Minimum Spanning Tree — Prim
# Returns total MST weight, or -1 if the graph is disconnected.
# ---------------------------------------------------------------------------

def prim_mst(args):
    n, edges = args[0], args[1]
    if n == 0:
        return 0

    # Build undirected adjacency list.
    adj = [[] for _ in range(n)]
    for e in edges:
        u, v, w = e[0], e[1], e[2]
        adj[u].append((w, v))
        adj[v].append((w, u))

    in_tree = [False] * n
    in_tree[0] = True
    heap = list(adj[0])  # (weight, node)
    heapq.heapify(heap)

    total_w = 0
    count = 1

    while heap and count < n:
        w, u = heapq.heappop(heap)
        if in_tree[u]:
            continue
        in_tree[u] = True
        total_w += w
        count += 1
        for edge in adj[u]:
            if not in_tree[edge[1]]:
                heapq.heappush(heap, edge)

    return total_w if count == n else -1


# ---------------------------------------------------------------------------
# Floyd-Warshall — all-pairs shortest paths
# Returns a flat n*n row-major list of distances (INF = 1<<60).
# ---------------------------------------------------------------------------

def floyd_warshall(args):
    n, edges = args[0], args[1]

    dist = [[INF] * n for _ in range(n)]
    for i in range(n):
        dist[i][i] = 0
    for e in edges:
        u, v, w = e[0], e[1], e[2]
        if w < dist[u][v]:
            dist[u][v] = w

    for k in range(n):
        for i in range(n):
            if dist[i][k] >= INF:
                continue
            for j in range(n):
                if dist[k][j] >= INF:
                    continue
                nd = dist[i][k] + dist[k][j]
                if nd < dist[i][j]:
                    dist[i][j] = nd

    # Flatten row-major.
    return [dist[i][j] for i in range(n) for j in range(n)]


# ---------------------------------------------------------------------------
# Graph Valid Tree
# Returns True iff n nodes and given undirected edges form a valid tree.
# ---------------------------------------------------------------------------

def graph_valid_tree(args):
    n, edges = args[0], args[1]
    if n == 0:
        return True
    if len(edges) != n - 1:
        return False

    parent = list(range(n))
    rank = [0] * n

    for e in edges:
        u, v = e[0], e[1]
        if not _union(parent, rank, u, v):
            return False  # cycle

    # Check connectivity: all nodes share one root.
    root = _find(parent, 0)
    return all(_find(parent, i) == root for i in range(n))


ORACLES = {
    "dijkstra":           dijkstra,
    "bellman_ford":       bellman_ford,
    "kruskal_mst":        kruskal_mst,
    "prim_mst":           prim_mst,
    "floyd_warshall":     floyd_warshall,
    "graph_valid_tree":   graph_valid_tree,
}
