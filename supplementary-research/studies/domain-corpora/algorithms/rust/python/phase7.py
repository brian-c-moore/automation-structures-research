"""Phase 7 — Linked List, Tries, Graphs: idiomatic Python oracles.

Independent of the Rust primitive implementations under test.

I/O encoding (identical to Rust):

  reverse_linked_list:     ints_list -> ints_list
  linked_list_cycle:       [ints_list, pos_int] -> bool
  merge_two_sorted_lists:  [ints_list, ints_list] -> ints_list
  merge_k_sorted_lists:    [ints_list, ...] -> ints_list
  reorder_list:            ints_list -> ints_list
  implement_trie:          [[op_str, word_str], ...] -> [bool, ...]  (one bool per query op)
  add_search_words:        [[op_str, word_str], ...] -> [bool, ...]  (one bool per "search" op)
  word_search_ii:          [[grid_rows], [word_strs]] -> sorted int list (indices of found words)
  number_of_islands:       [[row_of_single_char_strs], ...] -> int
  clone_graph:             [[adj_row], ...] -> [[adj_row], ...]  (sorted neighbours per node)
  pacific_atlantic:        [[elev_row], ...] -> [[row,col], ...]  (SetOfIntLists)
  course_schedule:         [n_int, [a,b], ...] -> bool
"""

import heapq
from collections import deque


# ---------------------------------------------------------------------------
# Reverse Linked List
# ---------------------------------------------------------------------------
def reverse_linked_list(nodes):
    return nodes[::-1]


# ---------------------------------------------------------------------------
# Linked List Cycle  (Floyd tortoise-and-hare)
#
# Input: [node_values_list, pos]  (pos = cycle-entry index, -1 = no cycle)
# ---------------------------------------------------------------------------
def linked_list_cycle(args):
    nodes, pos = args
    n = len(nodes)
    if n == 0:
        return False

    def succ(i):
        if i + 1 < n:
            return i + 1
        return pos if pos >= 0 else None

    slow, fast = 0, 0
    while True:
        slow = succ(slow)
        if slow is None:
            return False
        fast = succ(fast)
        if fast is None:
            return False
        fast = succ(fast)
        if fast is None:
            return False
        if slow == fast:
            return True


# ---------------------------------------------------------------------------
# Merge Two Sorted Lists
# ---------------------------------------------------------------------------
def merge_two_sorted_lists(args):
    a, b = args
    out = []
    i = j = 0
    while i < len(a) and j < len(b):
        if a[i] <= b[j]:
            out.append(a[i]); i += 1
        else:
            out.append(b[j]); j += 1
    out.extend(a[i:])
    out.extend(b[j:])
    return out


# ---------------------------------------------------------------------------
# Merge K Sorted Lists
# ---------------------------------------------------------------------------
def merge_k_sorted_lists(lists):
    heap = []
    for li, lst in enumerate(lists):
        if lst:
            heapq.heappush(heap, (lst[0], li, 0))
    out = []
    while heap:
        val, li, pos = heapq.heappop(heap)
        out.append(val)
        nxt = pos + 1
        if nxt < len(lists[li]):
            heapq.heappush(heap, (lists[li][nxt], li, nxt))
    return out


# ---------------------------------------------------------------------------
# Reorder List
# ---------------------------------------------------------------------------
def reorder_list(nodes):
    n = len(nodes)
    if n <= 1:
        return nodes[:]
    # Phase 1: find midpoint
    mid = (n - 1) // 2
    # Phase 2: reverse second half
    first = nodes[:mid + 1]
    second = nodes[mid + 1:][::-1]
    # Phase 3: interleave
    out = []
    i = j = 0
    turn = True
    while i < len(first) or j < len(second):
        if turn and i < len(first):
            out.append(first[i]); i += 1
        elif j < len(second):
            out.append(second[j]); j += 1
        elif i < len(first):
            out.append(first[i]); i += 1
        turn = not turn
    return out


# ---------------------------------------------------------------------------
# Implement Trie
#
# Op stream: [["insert","word"], ["search","w"], ["startsWith","app"], ...]
# Output: list of bool per query op ("search" / "startsWith").
# ---------------------------------------------------------------------------
def implement_trie(ops):
    root = {}  # nested dicts, "_end" marks terminal
    results = []

    def insert(word):
        node = root
        for ch in word:
            node = node.setdefault(ch, {})
        node["_end"] = True

    def search(word):
        node = root
        for ch in word:
            if ch not in node:
                return False
            node = node[ch]
        return "_end" in node

    def starts_with(prefix):
        node = root
        for ch in prefix:
            if ch not in node:
                return False
            node = node[ch]
        return True

    for op, word in ops:
        if op == "insert":
            insert(word)
        elif op == "search":
            results.append(search(word))
        elif op == "startsWith":
            results.append(starts_with(word))
    return results


# ---------------------------------------------------------------------------
# Add and Search Words (with wildcards)
#
# Op stream: [["addWord","bad"], ["search",".ad"], ...]
# Output: list of bool per "search" op.
# ---------------------------------------------------------------------------
def add_search_words(ops):
    root = {}
    results = []

    def add_word(word):
        node = root
        for ch in word:
            node = node.setdefault(ch, {})
        node["_end"] = True

    def search(word):
        def dfs(node, i):
            if i == len(word):
                return "_end" in node
            ch = word[i]
            if ch == ".":
                return any(dfs(node[c], i + 1) for c in node if c != "_end")
            if ch not in node:
                return False
            return dfs(node[ch], i + 1)
        return dfs(root, 0)

    for op, word in ops:
        if op in ("addWord", "insert"):
            add_word(word)
        elif op == "search":
            results.append(search(word))
    return results


# ---------------------------------------------------------------------------
# Word Search II
#
# Input: [[grid_rows], [word_strs]]
# Output: sorted list of 0-based indices (into words) of found words.
# ---------------------------------------------------------------------------
def word_search_ii(args):
    grid_rows, words = args
    if not grid_rows or not words:
        return []
    grid = [list(r) for r in grid_rows]
    rows, cols = len(grid), len(grid[0])

    # Build trie
    root = {}
    for idx, word in enumerate(words):
        node = root
        for ch in word:
            node = node.setdefault(ch, {})
        node.setdefault("_indices", set()).add(idx)

    found_indices = set()

    def dfs(node, r, c, path):
        ch = grid[r][c]
        if ch not in node:
            return
        nxt = node[ch]
        if "_indices" in nxt:
            found_indices.update(nxt["_indices"])
        grid[r][c] = "#"  # mark visited (paired undo below)
        for dr, dc in ((-1, 0), (1, 0), (0, -1), (0, 1)):
            nr, nc = r + dr, c + dc
            if 0 <= nr < rows and 0 <= nc < cols and grid[nr][nc] != "#":
                dfs(nxt, nr, nc, path + ch)
        grid[r][c] = ch  # undo

    for r in range(rows):
        for c in range(cols):
            dfs(root, r, c, "")

    return sorted(found_indices)


# ---------------------------------------------------------------------------
# Number of Islands
#
# Input: list of lists of single-char strings ("1" / "0").
# ---------------------------------------------------------------------------
def number_of_islands(grid_raw):
    if not grid_raw:
        return 0
    grid = [[cell for cell in row] for row in grid_raw]
    rows, cols = len(grid), len(grid[0])
    visited = set()
    count = 0

    def bfs(r, c):
        q = deque([(r, c)])
        visited.add((r, c))
        while q:
            cr, cc = q.popleft()
            for dr, dc in ((-1, 0), (1, 0), (0, -1), (0, 1)):
                nr, nc = cr + dr, cc + dc
                if 0 <= nr < rows and 0 <= nc < cols and (nr, nc) not in visited and grid[nr][nc] == "1":
                    visited.add((nr, nc))
                    q.append((nr, nc))

    for r in range(rows):
        for c in range(cols):
            if grid[r][c] == "1" and (r, c) not in visited:
                bfs(r, c)
                count += 1
    return count


# ---------------------------------------------------------------------------
# Clone Graph
#
# Input: adjacency list [[neighbours_of_0], [neighbours_of_1], ...]
# Output: same format (sorted neighbours per node, node order preserved).
# ---------------------------------------------------------------------------
def clone_graph(adj):
    if not adj:
        return []
    n = len(adj)
    cloned = [sorted(adj[i]) for i in range(n)]
    return cloned


# ---------------------------------------------------------------------------
# Pacific Atlantic Water Flow
#
# Input: elevation grid [[int, ...], ...]
# Output: sorted list of [row, col] pairs (SetOfIntLists).
# ---------------------------------------------------------------------------
def pacific_atlantic(heights):
    if not heights:
        return []
    rows, cols = len(heights), len(heights[0])

    def bfs(sources):
        visited = set(sources)
        q = deque(sources)
        while q:
            r, c = q.popleft()
            for dr, dc in ((-1, 0), (1, 0), (0, -1), (0, 1)):
                nr, nc = r + dr, c + dc
                if 0 <= nr < rows and 0 <= nc < cols and (nr, nc) not in visited \
                        and heights[nr][nc] >= heights[r][c]:
                    visited.add((nr, nc))
                    q.append((nr, nc))
        return visited

    pac = bfs([(0, c) for c in range(cols)] + [(r, 0) for r in range(1, rows)])
    atl = bfs([(rows - 1, c) for c in range(cols)] + [(r, cols - 1) for r in range(rows - 1)])
    result = sorted([r, c] for r, c in pac & atl)
    return result


# ---------------------------------------------------------------------------
# Course Schedule  (Kahn's topological sort)
#
# Input: [n, [a, b], ...]  (b must precede a)
# Output: bool (can all courses be finished?)
# ---------------------------------------------------------------------------
def course_schedule(args):
    n = args[0]
    if n == 0:
        return True
    prereqs = args[1:]
    in_deg = [0] * n
    adj = [[] for _ in range(n)]
    for pair in prereqs:
        a, b = pair[0], pair[1]
        if 0 <= a < n and 0 <= b < n and a != b:
            adj[b].append(a)
            in_deg[a] += 1
    q = deque(i for i in range(n) if in_deg[i] == 0)
    count = 0
    while q:
        node = q.popleft()
        count += 1
        for dep in adj[node]:
            in_deg[dep] -= 1
            if in_deg[dep] == 0:
                q.append(dep)
    return count == n


ORACLES = {
    "reverse_linked_list":      reverse_linked_list,
    "linked_list_cycle":        linked_list_cycle,
    "merge_two_sorted_lists":   merge_two_sorted_lists,
    "merge_k_sorted_lists":     merge_k_sorted_lists,
    "reorder_list":             reorder_list,
    "implement_trie":           implement_trie,
    "add_search_words":         add_search_words,
    "word_search_ii":           word_search_ii,
    "number_of_islands":        number_of_islands,
    "clone_graph":              clone_graph,
    "pacific_atlantic":         pacific_atlantic,
    "course_schedule":          course_schedule,
}
