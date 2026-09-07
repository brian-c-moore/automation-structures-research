"""Phase 5 — Trees and Heap / Priority Queue: idiomatic Python
reference oracles.

Independent of the Rust primitive implementations under test. Each
oracle is the classic textbook formulation. This module exposes
`ORACLES` (name -> fn); the shared `oracles.py` dispatcher handles the
JSON stdin/stdout protocol.

## Tree encoding (identical in Rust and Python)

The tree is represented as a **level-order array**. Index 0 is the
root; the children of the node at index i are at indices 2*i+1 (left)
and 2*i+2 (right). A missing node is the sentinel NULL_NODE = -100000.
Input values stay in [-9999, 9999], well away from the sentinel.
"""

import heapq

NULL_NODE = -100000


# ---------------------------------------------------------------------------
# Tree helpers
# ---------------------------------------------------------------------------

def is_live(arr, i):
    return i < len(arr) and arr[i] != NULL_NODE


def children(arr, i):
    kids = []
    l, r = 2 * i + 1, 2 * i + 2
    if is_live(arr, l):
        kids.append(l)
    if is_live(arr, r):
        kids.append(r)
    return kids


# ---------------------------------------------------------------------------
# Invert Binary Tree
# BFS + swap children at each node.
# Output: level-order array (same encoding).
# ---------------------------------------------------------------------------
def invert_binary_tree(arr):
    if not arr or arr[0] == NULL_NODE:
        return list(arr)
    arr = list(arr)
    from collections import deque
    q = deque([0])
    while q:
        i = q.popleft()
        l, r = 2 * i + 1, 2 * i + 2
        # Ensure capacity
        while len(arr) <= max(l, r):
            arr.append(NULL_NODE)
        arr[l], arr[r] = arr[r], arr[l]
        for c in children(arr, i):
            q.append(c)
    # Trim trailing sentinels
    while arr and arr[-1] == NULL_NODE:
        arr.pop()
    return arr


# ---------------------------------------------------------------------------
# Maximum Depth of Binary Tree
# Post-order recursion: depth = 1 + max(left_depth, right_depth).
# ---------------------------------------------------------------------------
def max_depth(arr):
    if not arr or arr[0] == NULL_NODE:
        return 0

    def dfs(i):
        if not is_live(arr, i):
            return 0
        return 1 + max(dfs(2 * i + 1), dfs(2 * i + 2))

    return dfs(0)


# ---------------------------------------------------------------------------
# Same Tree
# Input: [arrA, arrB]  Output: bool
# ---------------------------------------------------------------------------
def same_tree(args):
    a, b = args

    def eq(i):
        la = is_live(a, i)
        lb = is_live(b, i)
        if la != lb:
            return False
        if not la:
            return True
        if a[i] != b[i]:
            return False
        return eq(2 * i + 1) and eq(2 * i + 2)

    return eq(0)


# ---------------------------------------------------------------------------
# Binary Tree Level Order Traversal
# BFS with level boundaries.
# Output: list of lists of ints.
# ---------------------------------------------------------------------------
def level_order(arr):
    if not arr or arr[0] == NULL_NODE:
        return []
    from collections import deque
    result = []
    q = deque([0])
    while q:
        level_size = len(q)
        level = []
        for _ in range(level_size):
            i = q.popleft()
            level.append(arr[i])
            for c in children(arr, i):
                q.append(c)
        result.append(level)
    return result


# ---------------------------------------------------------------------------
# Validate Binary Search Tree
# In-order traversal; check strictly increasing.
# ---------------------------------------------------------------------------
def validate_bst(arr):
    if not arr or arr[0] == NULL_NODE:
        return True
    prev = [None]
    valid = [True]

    def inorder(i):
        if not is_live(arr, i) or not valid[0]:
            return
        inorder(2 * i + 1)
        if prev[0] is not None and arr[i] <= prev[0]:
            valid[0] = False
        prev[0] = arr[i]
        inorder(2 * i + 2)

    inorder(0)
    return valid[0]


# ---------------------------------------------------------------------------
# Binary Tree Maximum Path Sum
# Post-order: at each node compute max single-direction gain and update
# global maximum with the through-node sum.
# ---------------------------------------------------------------------------
def max_path_sum(arr):
    if not arr or arr[0] == NULL_NODE:
        return 0
    best = [float('-inf')]

    def dfs(i):
        if not is_live(arr, i):
            return 0
        lg = max(dfs(2 * i + 1), 0)
        rg = max(dfs(2 * i + 2), 0)
        best[0] = max(best[0], arr[i] + lg + rg)
        return arr[i] + max(lg, rg)

    dfs(0)
    return best[0]


# ---------------------------------------------------------------------------
# Kth Largest in Stream
# Input: [k, [[kind, val], ...]]
# kind=0 → add; kind=1 → add then query
# Output: list of query results
# ---------------------------------------------------------------------------
def kth_largest_stream(args):
    k, ops = args
    # min-heap of size k
    heap = []
    results = []
    for op in ops:
        kind, val = op
        heapq.heappush(heap, val)
        if len(heap) > k:
            heapq.heappop(heap)
        if kind == 1:
            results.append(heap[0])
    return results


# ---------------------------------------------------------------------------
# Last Stone Weight
# Max-heap smash simulation.
# ---------------------------------------------------------------------------
def last_stone_weight(stones):
    if not stones:
        return 0
    heap = [-s for s in stones]
    heapq.heapify(heap)
    while len(heap) >= 2:
        a = -heapq.heappop(heap)
        b = -heapq.heappop(heap)
        if a != b:
            heapq.heappush(heap, -(a - b))
    return -heap[0] if heap else 0


# ---------------------------------------------------------------------------
# K Closest Points to Origin
# Input: [[[x,y], ...], k]
# Output: list of k closest points (sorted for SetOfIntLists equiv)
# ---------------------------------------------------------------------------
def k_closest_points(args):
    points, k = args
    if k == 0 or not points:
        return []
    pts = sorted(points, key=lambda p: p[0] * p[0] + p[1] * p[1])
    return [list(p) for p in pts[:k]]


# ---------------------------------------------------------------------------
# Find Median from Data Stream
# Input: [[kind, val], ...]  kind=0 → add, kind=1 → query
# Output: list of (median * 2) as ints  [matches Rust encoding]
# ---------------------------------------------------------------------------
def find_median_stream(ops):
    # lo: max-heap (lower half, stored negated); hi: min-heap (upper half)
    lo = []  # max-heap via negation
    hi = []  # min-heap
    results = []
    for op in ops:
        kind, val = op
        if kind == 0:
            if not lo or val <= -lo[0]:
                heapq.heappush(lo, -val)
            else:
                heapq.heappush(hi, val)
            # Rebalance
            if len(lo) > len(hi) + 1:
                heapq.heappush(hi, -heapq.heappop(lo))
            elif len(hi) > len(lo):
                heapq.heappush(lo, -heapq.heappop(hi))
        else:
            if len(lo) == len(hi):
                median_x2 = (-lo[0] if lo else 0) + (hi[0] if hi else 0)
            else:
                median_x2 = (-lo[0]) * 2
            results.append(median_x2)
    return results


# ---------------------------------------------------------------------------
# Dispatch wrappers — convert JSON-decoded Value structure to native types.
#
# The wire format from Rust's Value::to_json() sends ints as ints, lists
# as lists, bools as bools. Python oracles receive plain Python objects.
# ---------------------------------------------------------------------------

def _invert_binary_tree(inp):
    return invert_binary_tree(inp)


def _max_depth(inp):
    return max_depth(inp)


def _same_tree(inp):
    # inp = [arrA, arrB]
    return same_tree(inp)


def _level_order(inp):
    return level_order(inp)


def _validate_bst(inp):
    return validate_bst(inp)


def _max_path_sum(inp):
    return max_path_sum(inp)


def _kth_largest_stream(inp):
    # inp = [k, [[kind,val],...]]
    k = inp[0]
    ops = [[o[0], o[1]] for o in inp[1]]
    return kth_largest_stream([k, ops])


def _last_stone_weight(inp):
    return last_stone_weight(inp)


def _k_closest_points(inp):
    # inp = [[[x,y],...], k]
    pts = [list(p) for p in inp[0]]
    k = inp[1]
    return k_closest_points([pts, k])


def _find_median_stream(inp):
    # inp = [[kind,val],...]
    ops = [[o[0], o[1]] for o in inp]
    return find_median_stream(ops)


ORACLES = {
    "invert_binary_tree":  _invert_binary_tree,
    "max_depth":           _max_depth,
    "same_tree":           _same_tree,
    "level_order":         _level_order,
    "validate_bst":        _validate_bst,
    "max_path_sum":        _max_path_sum,
    "kth_largest_stream":  _kth_largest_stream,
    "last_stone_weight":   _last_stone_weight,
    "k_closest_points":    _k_closest_points,
    "find_median_stream":  _find_median_stream,
}
