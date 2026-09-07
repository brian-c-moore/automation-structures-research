"""Phase 8 — Greedy, Intervals, Math & Geometry, Bit Manipulation:
idiomatic Python reference oracles.

Independent of the Rust primitive implementations under test.
This module exposes `ORACLES` (name -> fn); the shared `oracles.py`
dispatcher handles the JSON stdin/stdout protocol.

I/O CONTRACT (matches Rust encoding exactly):
  Kadane      : list[int]                        -> int
  Jump Game   : list[int]                        -> bool
  Gas Station : [list[int], list[int]]           -> int  (-1 if impossible)
  Hand        : [list[int], int]                 -> bool
  Merge IV    : list[[s,e], ...]                 -> list[[s,e], ...]
  Insert IV   : list[[s,e], ..., [new_s,new_e]] -> list[[s,e], ...]
  Non-overlap : list[[s,e], ...]                 -> int
  Meeting II  : list[[s,e], ...]                 -> int
  Rotate      : list[list[int]] (NxN)            -> list[list[int]]
  Spiral      : list[list[int]] (MxN)            -> list[int]
  Set Zeroes  : list[list[int]]                  -> list[list[int]]
  Pow(x,n)   : [int base, int exp]              -> int  (non-negative exp)
  Happy       : int                              -> bool
  Hamming     : int (as u32)                     -> int
  Single      : list[int]                        -> int
  Missing     : list[int]                        -> int
  CountBits   : int N                            -> list[int] (0..=N)
  ReverseBits : int (as u32)                     -> int
"""

import heapq


# ──────────────────────────────────────────────────────────────────────────────
# Greedy
# ──────────────────────────────────────────────────────────────────────────────

def maximum_subarray(nums):
    if not nums:
        return 0
    best_here = best_overall = nums[0]
    for x in nums[1:]:
        best_here = max(best_here + x, x)
        best_overall = max(best_overall, best_here)
    return best_overall


def jump_game(nums):
    if not nums:
        return True
    furthest = 0
    n = len(nums)
    for i in range(n):
        if i > furthest:
            return False
        furthest = max(furthest, i + nums[i])
    return furthest >= n - 1


def gas_station(args):
    gas, cost = args
    n = len(gas)
    if n == 0:
        return -1
    total_net = sum(g - c for g, c in zip(gas, cost))
    if total_net < 0:
        return -1
    net = 0
    start = 0
    for i in range(n):
        net += gas[i] - cost[i]
        if net < 0:
            start = i + 1
            net = 0
    return start


def hand_of_straights(args):
    hand, w = args
    if w == 0:
        return True
    if len(hand) % w != 0:
        return False
    counts = {}
    for c in hand:
        counts[c] = counts.get(c, 0) + 1
    for k in sorted(counts):
        cnt = counts.get(k, 0)
        if cnt == 0:
            continue
        for j in range(w):
            need = k + j
            if counts.get(need, 0) < cnt:
                return False
            counts[need] -= cnt
    return True


# ──────────────────────────────────────────────────────────────────────────────
# Intervals
# ──────────────────────────────────────────────────────────────────────────────

def merge_intervals(intervals):
    if not intervals:
        return []
    ivs = sorted([list(iv) for iv in intervals])
    merged = [ivs[0]]
    for s, e in ivs[1:]:
        if s <= merged[-1][1]:
            merged[-1][1] = max(merged[-1][1], e)
        else:
            merged.append([s, e])
    return merged


def insert_interval(intervals):
    """intervals: sorted non-overlapping list with the new interval as last element."""
    if not intervals:
        return []
    *existing, new_iv = intervals
    ns, ne = new_iv
    result = []
    inserted = False
    for s, e in existing:
        if e < ns:
            result.append([s, e])
        elif s > ne:
            if not inserted:
                result.append([ns, ne])
                inserted = True
            result.append([s, e])
        else:
            ns = min(ns, s)
            ne = max(ne, e)
    if not inserted:
        result.append([ns, ne])
    return result


def non_overlapping_intervals(intervals):
    if not intervals:
        return 0
    ivs = sorted(intervals, key=lambda iv: iv[1])
    n = len(ivs)
    kept = 0
    last_end = float("-inf")
    for s, e in ivs:
        if s >= last_end:
            kept += 1
            last_end = e
    return n - kept


def meeting_rooms_ii(intervals):
    if not intervals:
        return 0
    ivs = sorted(intervals, key=lambda iv: iv[0])
    heap = []  # min-heap of end times
    max_rooms = 0
    for s, e in ivs:
        if heap and heap[0] <= s:
            heapq.heapreplace(heap, e)
        else:
            heapq.heappush(heap, e)
        max_rooms = max(max_rooms, len(heap))
    return max_rooms


# ──────────────────────────────────────────────────────────────────────────────
# Math & Geometry
# ──────────────────────────────────────────────────────────────────────────────

def rotate_image(matrix):
    if not matrix:
        return []
    n = len(matrix)
    mat = [list(row) for row in matrix]
    # Transpose
    for i in range(n):
        for j in range(i + 1, n):
            mat[i][j], mat[j][i] = mat[j][i], mat[i][j]
    # Reverse each row
    for row in mat:
        row.reverse()
    return mat


def spiral_matrix(matrix):
    if not matrix:
        return []
    res = []
    top, bottom, left, right = 0, len(matrix) - 1, 0, len(matrix[0]) - 1
    while top <= bottom and left <= right:
        for c in range(left, right + 1):
            res.append(matrix[top][c])
        top += 1
        for r in range(top, bottom + 1):
            res.append(matrix[r][right])
        right -= 1
        if top <= bottom:
            for c in range(right, left - 1, -1):
                res.append(matrix[bottom][c])
            bottom -= 1
        if left <= right:
            for r in range(bottom, top - 1, -1):
                res.append(matrix[r][left])
            left += 1
    return res


def set_matrix_zeroes(matrix):
    if not matrix:
        return []
    mat = [list(row) for row in matrix]
    m, n = len(mat), len(mat[0])
    zero_rows = [False] * m
    zero_cols = [False] * n
    for i in range(m):
        for j in range(n):
            if mat[i][j] == 0:
                zero_rows[i] = True
                zero_cols[j] = True
    for i in range(m):
        for j in range(n):
            if zero_rows[i] or zero_cols[j]:
                mat[i][j] = 0
    return mat


def pow_xn(args):
    """Integer base, non-negative exponent -> exact integer result."""
    base, exp = args
    exp = max(exp, 0)
    result = 1
    cur = base
    while exp > 0:
        if exp & 1:
            result *= cur
        cur *= cur
        exp >>= 1
    return result


def happy_number(n):
    n = max(abs(n), 1)

    def step(x):
        s = 0
        while x > 0:
            d = x % 10
            s += d * d
            x //= 10
        return s

    slow = n
    fast = step(n)
    while fast != 1 and slow != fast:
        slow = step(slow)
        fast = step(step(fast))
    return fast == 1


# ──────────────────────────────────────────────────────────────────────────────
# Bit Manipulation
# ──────────────────────────────────────────────────────────────────────────────

def hamming_weight(n):
    """Count 1-bits in n (treated as uint32)."""
    n = n & 0xFFFFFFFF
    count = 0
    while n:
        n &= n - 1
        count += 1
    return count


def single_number(nums):
    result = 0
    for x in nums:
        result ^= x
    return result


def missing_number(nums):
    n = len(nums)
    xor_idx = 0
    for i in range(n + 1):
        xor_idx ^= i
    xor_val = 0
    for x in nums:
        xor_val ^= x
    return xor_idx ^ xor_val


def counting_bits(n):
    n = max(n, 0)
    dp = [0] * (n + 1)
    for i in range(1, n + 1):
        dp[i] = dp[i >> 1] + (i & 1)
    return dp


def reverse_bits(n):
    """Reverse the 32-bit representation of n."""
    n = n & 0xFFFFFFFF
    result = 0
    for _ in range(32):
        result = (result << 1) | (n & 1)
        n >>= 1
    return result


ORACLES = {
    "maximum_subarray":          maximum_subarray,
    "jump_game":                 jump_game,
    "gas_station":               gas_station,
    "hand_of_straights":         hand_of_straights,
    "merge_intervals":           merge_intervals,
    "insert_interval":           insert_interval,
    "non_overlapping_intervals": non_overlapping_intervals,
    "meeting_rooms_ii":          meeting_rooms_ii,
    "rotate_image":              rotate_image,
    "spiral_matrix":             spiral_matrix,
    "set_matrix_zeroes":         set_matrix_zeroes,
    "pow_xn":                    pow_xn,
    "happy_number":              happy_number,
    "hamming_weight":            hamming_weight,
    "single_number":             single_number,
    "missing_number":            missing_number,
    "counting_bits":             counting_bits,
    "reverse_bits":              reverse_bits,
}
