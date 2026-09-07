"""Phase 6 — Arrays & Hashing, Two Pointers, Sliding Window.

Independent idiomatic Python reference oracles. Each oracle is the
classic textbook formulation, written without reference to the Rust
primitive framework. Exposes `ORACLES` (name -> fn).

I/O encoding (mirrors Rust Value encoding):
  - Contains Duplicate / Valid Palindrome -> bool
  - Two Sum input [ints, target] -> two indices sorted ascending as list
  - Two Sum II same shape as Two Sum
  - Three Sum -> list of sorted triplets (list-of-lists), SetOfIntLists
  - Group Anagrams input list[str] -> list-of-groups of indices, SetOfIntLists
  - Top K Frequent input [ints, k] -> the k values as list, MultisetInt
  - Product Except Self / Sliding Window Max -> list of ints, Exact
  - Scalars (Longest Consecutive, Container With Most Water, etc.) -> int
  - Strings (Min Window Substring) -> str
  - Char Replacement input [str, k] -> int
"""

# ---------------------------------------------------------------------------
# Arrays & Hashing
# ---------------------------------------------------------------------------

def contains_duplicate(nums):
    seen = set()
    for x in nums:
        if x in seen:
            return True
        seen.add(x)
    return False


def two_sum(args):
    nums, target = args
    comp = {}
    for i, x in enumerate(nums):
        complement = target - x
        if complement in comp:
            pair = sorted([comp[complement], i])
            return pair
        if x not in comp:
            comp[x] = i
    return []


def group_anagrams(strs):
    """Input: list of strings. Output: list-of-groups-of-indices."""
    from collections import defaultdict
    buckets = defaultdict(list)
    for i, s in enumerate(strs):
        key = tuple(sorted(s))
        buckets[key].append(i)
    return [sorted(g) for g in buckets.values()]


def top_k_frequent(args):
    nums, k = args
    from collections import Counter
    c = Counter(nums)
    # Sort deterministically: descending count, then ascending value on ties.
    # This matches the Rust CompetitiveSelection score = count*SCALE - value.
    ranked = sorted(c.items(), key=lambda p: (-p[1], p[0]))
    return [x for x, _ in ranked[:k]]


def product_except_self(nums):
    n = len(nums)
    if n == 0:
        return []
    left = [1] * n
    for i in range(1, n):
        left[i] = left[i - 1] * nums[i - 1]
    right = 1
    out = [0] * n
    for i in range(n - 1, -1, -1):
        out[i] = left[i] * right
        right *= nums[i]
    return out


def longest_consecutive(nums):
    s = set(nums)
    best = 0
    for x in s:
        if x - 1 not in s:
            cur = x
            length = 0
            while cur in s:
                cur += 1
                length += 1
            best = max(best, length)
    return best


# ---------------------------------------------------------------------------
# Two Pointers
# ---------------------------------------------------------------------------

def valid_palindrome(s):
    filtered = [c.lower() for c in s if c.isalnum()]
    return filtered == filtered[::-1]


def two_sum_ii(args):
    nums, target = args
    lo, hi = 0, len(nums) - 1
    while lo < hi:
        s = nums[lo] + nums[hi]
        if s == target:
            pair = sorted([lo, hi])
            return pair
        elif s < target:
            lo += 1
        else:
            hi -= 1
    return []


def three_sum(nums):
    nums = sorted(nums)
    n = len(nums)
    result = []
    seen = set()
    for i in range(n):
        if i > 0 and nums[i] == nums[i - 1]:
            continue
        lo, hi = i + 1, n - 1
        while lo < hi:
            s = nums[i] + nums[lo] + nums[hi]
            if s == 0:
                key = (nums[i], nums[lo], nums[hi])
                if key not in seen:
                    seen.add(key)
                    result.append(sorted([nums[i], nums[lo], nums[hi]]))
                lo += 1
                hi -= 1
            elif s < 0:
                lo += 1
            else:
                hi -= 1
    return result


def container_with_most_water(heights):
    lo, hi = 0, len(heights) - 1
    best = 0
    while lo < hi:
        area = (hi - lo) * min(heights[lo], heights[hi])
        best = max(best, area)
        if heights[lo] < heights[hi]:
            lo += 1
        else:
            hi -= 1
    return best


def trapping_rain_water(heights):
    if len(heights) < 2:
        return 0
    lo, hi = 0, len(heights) - 1
    left_max = right_max = 0
    total = 0
    while lo < hi:
        if heights[lo] <= heights[hi]:
            left_max = max(left_max, heights[lo])
            total += left_max - heights[lo]
            lo += 1
        else:
            right_max = max(right_max, heights[hi])
            total += right_max - heights[hi]
            hi -= 1
    return total


# ---------------------------------------------------------------------------
# Sliding Window
# ---------------------------------------------------------------------------

def buy_sell_stock(prices):
    min_p = float("inf")
    best = 0
    for p in prices:
        min_p = min(min_p, p)
        best = max(best, p - min_p)
    return best


def longest_no_repeat(s):
    last = {}
    lo = 0
    best = 0
    for hi, c in enumerate(s):
        if c in last and last[c] >= lo:
            lo = last[c] + 1
        last[c] = hi
        best = max(best, hi - lo + 1)
    return best


def char_replacement(args):
    s, k = args
    counts = {}
    lo = 0
    max_count = 0
    best = 0
    for hi, c in enumerate(s):
        counts[c] = counts.get(c, 0) + 1
        max_count = max(max_count, counts[c])
        while (hi - lo + 1) - max_count > k:
            counts[s[lo]] -= 1
            lo += 1
        best = max(best, hi - lo + 1)
    return best


def min_window_substring(args):
    s, t = args
    if not t:
        return ""
    from collections import Counter
    required = Counter(t)
    need = len(required)
    window = {}
    satisfied = 0
    lo = 0
    best_len = float("inf")
    best_start = 0
    for hi, c in enumerate(s):
        window[c] = window.get(c, 0) + 1
        if c in required and window[c] == required[c]:
            satisfied += 1
        while satisfied == need:
            win = hi - lo + 1
            if win < best_len:
                best_len = win
                best_start = lo
            lc = s[lo]
            window[lc] -= 1
            if lc in required and window[lc] < required[lc]:
                satisfied -= 1
            lo += 1
    return s[best_start:best_start + best_len] if best_len != float("inf") else ""


def sliding_window_max(args):
    nums, k = args
    from collections import deque
    k = max(1, k)
    n = len(nums)
    if n == 0:
        return []
    dq = deque()
    result = []
    for i in range(n):
        while dq and nums[dq[-1]] <= nums[i]:
            dq.pop()
        dq.append(i)
        if dq[0] + k <= i:
            dq.popleft()
        if i + 1 >= k:
            result.append(nums[dq[0]])
    return result


ORACLES = {
    "contains_duplicate":        contains_duplicate,
    "two_sum":                   two_sum,
    "group_anagrams":            group_anagrams,
    "top_k_frequent":            top_k_frequent,
    "product_except_self":       product_except_self,
    "longest_consecutive":       longest_consecutive,
    "valid_palindrome":          valid_palindrome,
    "two_sum_ii":                two_sum_ii,
    "three_sum":                 three_sum,
    "container_with_most_water": container_with_most_water,
    "trapping_rain_water":       trapping_rain_water,
    "buy_sell_stock":            buy_sell_stock,
    "longest_no_repeat":         longest_no_repeat,
    "char_replacement":          char_replacement,
    "min_window_substring":      min_window_substring,
    "sliding_window_max":        sliding_window_max,
}
