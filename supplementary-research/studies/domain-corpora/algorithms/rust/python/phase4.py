"""Phase 4 — Backtracking: idiomatic Python reference oracles.

Independent of the Rust primitive implementations under test.
Each oracle is the classic textbook formulation.

## I/O encoding (Python == Rust)

| Oracle          | Input (decoded from JSON)               | Output             |
|-----------------|-----------------------------------------|--------------------|
| subsets         | list[int]                               | list[list[int]]    |
| combination_sum | [list[int] cands, int target]           | list[list[int]]    |
| permutations    | list[int]                               | list[list[int]]    |
| word_search     | [list[str] grid_rows, str word]         | bool               |
| n_queens        | int n                                   | int (count)        |

SetOfIntLists outputs: inner lists are canonicalized (sorted) and outer
order is insignificant; the Rust equivalence.Equiv.SetOfIntLists relation
handles this.  The Python oracles return unsorted inner lists; the
harness canonicalizes both sides.
"""


def subsets(nums):
    """All 2^n subsets of distinct integers."""
    result = []

    def bt(start, current):
        result.append(list(current))
        for i in range(start, len(nums)):
            current.append(nums[i])
            bt(i + 1, current)
            current.pop()

    bt(0, [])
    return result


def combination_sum(args):
    """Combinations (with reuse) of distinct positive integers summing to target."""
    cands, target = args
    result = []

    def bt(start, remaining, current):
        if remaining == 0:
            result.append(list(current))
            return
        for i in range(start, len(cands)):
            if cands[i] <= remaining:
                current.append(cands[i])
                bt(i, remaining - cands[i], current)  # reuse allowed: same i
                current.pop()

    bt(0, target, [])
    return result


def permutations(nums):
    """All permutations of distinct integers."""
    result = []
    used = [False] * len(nums)

    def bt(current):
        if len(current) == len(nums):
            result.append(list(current))
            return
        for i in range(len(nums)):
            if not used[i]:
                used[i] = True
                current.append(nums[i])
                bt(current)
                current.pop()
                used[i] = False

    bt([])
    return result


def word_search(args):
    """Return True iff word can be formed by adjacent cells in the grid."""
    grid_rows, word = args
    if not word:
        return True
    if not grid_rows or not grid_rows[0]:
        return False
    nrows = len(grid_rows)
    ncols = len(grid_rows[0])
    w = list(word)

    def dfs(r, c, depth, visited):
        if depth == len(w):
            return True
        if r < 0 or r >= nrows or c < 0 or c >= ncols:
            return False
        if (r, c) in visited:
            return False
        if grid_rows[r][c] != w[depth]:
            return False
        visited.add((r, c))
        for dr, dc in [(-1, 0), (1, 0), (0, -1), (0, 1)]:
            if dfs(r + dr, c + dc, depth + 1, visited):
                visited.discard((r, c))
                return True
        visited.discard((r, c))
        return False

    for sr in range(nrows):
        for sc in range(ncols):
            if grid_rows[sr][sc] == w[0]:
                if dfs(sr, sc, 0, set()):
                    return True
    return False


def n_queens(n):
    """Count distinct solutions to the N-Queens problem."""
    if n == 0:
        return 1  # one empty solution
    count = [0]
    cols = set()
    diags = set()
    antis = set()

    def bt(row):
        if row == n:
            count[0] += 1
            return
        for c in range(n):
            d = row - c
            a = row + c
            if c not in cols and d not in diags and a not in antis:
                cols.add(c)
                diags.add(d)
                antis.add(a)
                bt(row + 1)
                cols.discard(c)
                diags.discard(d)
                antis.discard(a)

    bt(0)
    return count[0]


ORACLES = {
    "subsets": subsets,
    "combination_sum": combination_sum,
    "permutations": permutations,
    "word_search": word_search,
    "n_queens": n_queens,
}
