"""Phase 2 — Stack and Binary Search: idiomatic Python reference oracles.

Independent of the Rust primitive implementations under test. Each oracle is
the classic textbook formulation, written without reference to the framework.

I/O encodings (must match phase2_stack_bsearch.rs exactly):

valid_parentheses   : str -> bool
min_stack           : List[List[int,int]] -> List[int]
                        op [0,v]=push(v), [1,0]=pop, [2,0]=top, [3,0]=getMin
                        output = list of int results for top/getMin ops only
eval_rpn            : List[str] -> int
daily_temperatures  : List[int] -> List[int]
largest_rect_histogram : List[int] -> int
binary_search       : [List[int], int] -> int  (index or -1)
search_rotated      : [List[int], int] -> int  (index or -1)
find_min_rotated    : List[int] -> int
koko_bananas        : [List[int], int] -> int
median_two_sorted   : [List[int], List[int]] -> int  (2 * median, integer encoding)
"""

import math


def valid_parentheses(s):
    stack = []
    match = {')': '(', ']': '[', '}': '{'}
    for c in s:
        if c in '([{':
            stack.append(c)
        else:
            if not stack or stack[-1] != match[c]:
                return False
            stack.pop()
    return len(stack) == 0


def min_stack(ops):
    # ops: list of [code, arg]
    # code 0=push, 1=pop, 2=top, 3=getMin
    main = []
    mins = []
    results = []
    for op in ops:
        code, arg = op[0], op[1]
        if code == 0:
            main.append(arg)
            mins.append(arg if not mins else min(arg, mins[-1]))
        elif code == 1:
            if main:
                main.pop()
                mins.pop()
        elif code == 2:
            if main:
                results.append(main[-1])
        elif code == 3:
            if mins:
                results.append(mins[-1])
    return results


def eval_rpn(tokens):
    stack = []
    for t in tokens:
        if t in ('+', '-', '*', '/'):
            b, a = stack.pop(), stack.pop()
            if t == '+':
                stack.append(a + b)
            elif t == '-':
                stack.append(a - b)
            elif t == '*':
                stack.append(a * b)
            else:
                # truncate toward zero (matches C int division)
                stack.append(int(a / b))
        else:
            stack.append(int(t))
    return stack[0]


def daily_temperatures(temps):
    n = len(temps)
    ans = [0] * n
    stack = []  # indices
    for i, t in enumerate(temps):
        while stack and temps[stack[-1]] < t:
            j = stack.pop()
            ans[j] = i - j
        stack.append(i)
    return ans


def largest_rect_histogram(heights):
    heights = list(heights) + [0]
    stack = []  # (start_idx, height)
    max_area = 0
    for i, h in enumerate(heights):
        start = i
        while stack and stack[-1][1] >= h:
            s_idx, s_h = stack.pop()
            max_area = max(max_area, s_h * (i - s_idx))
            start = s_idx
        if h > 0:
            stack.append((start, h))
    return max_area


def binary_search(args):
    arr, target = args
    lo, hi = 0, len(arr) - 1
    while lo <= hi:
        mid = (lo + hi) // 2
        if arr[mid] == target:
            return mid
        elif arr[mid] < target:
            lo = mid + 1
        else:
            hi = mid - 1
    return -1


def search_rotated(args):
    arr, target = args
    if not arr:
        return -1
    lo, hi = 0, len(arr) - 1
    while lo <= hi:
        mid = (lo + hi) // 2
        if arr[mid] == target:
            return mid
        # left half is sorted
        if arr[lo] <= arr[mid]:
            if arr[lo] <= target < arr[mid]:
                hi = mid - 1
            else:
                lo = mid + 1
        else:
            if arr[mid] < target <= arr[hi]:
                lo = mid + 1
            else:
                hi = mid - 1
    return -1


def find_min_rotated(arr):
    if not arr:
        return 0
    lo, hi = 0, len(arr) - 1
    while lo < hi:
        mid = (lo + hi) // 2
        if arr[mid] > arr[hi]:
            lo = mid + 1
        else:
            hi = mid
    return arr[lo]


def koko_bananas(args):
    piles, h = args
    if not piles:
        return 1
    lo, hi = 1, max(piles)
    while lo < hi:
        mid = (lo + hi) // 2
        hours = sum(math.ceil(p / mid) for p in piles)
        if hours <= h:
            hi = mid
        else:
            lo = mid + 1
    return lo


def median_two_sorted(args):
    """Return 2 * median as an integer (encoding matches Rust side)."""
    a, b = args
    # Ensure a is the smaller
    if len(a) > len(b):
        a, b = b, a
    m, n = len(a), len(b)
    total = m + n
    half = (total + 1) // 2

    lo, hi = 0, m
    while lo <= hi:
        i = (lo + hi) // 2
        j = half - i
        a_left  = a[i - 1] if i > 0 else float('-inf')
        a_right = a[i]     if i < m else float('inf')
        b_left  = b[j - 1] if j > 0 else float('-inf')
        b_right = b[j]     if j < n else float('inf')

        if a_left <= b_right and b_left <= a_right:
            max_left  = max(a_left, b_left)
            min_right = min(a_right, b_right)
            if total % 2 == 1:
                return int(max_left * 2)
            else:
                return int(max_left + min_right)
        elif a_left > b_right:
            hi = i - 1
        else:
            lo = i + 1
    # fallback (should not reach)
    return 0


ORACLES = {
    "valid_parentheses": valid_parentheses,
    "min_stack": min_stack,
    "eval_rpn": eval_rpn,
    "daily_temperatures": daily_temperatures,
    "largest_rect_histogram": largest_rect_histogram,
    "binary_search": binary_search,
    "search_rotated": search_rotated,
    "find_min_rotated": find_min_rotated,
    "koko_bananas": koko_bananas,
    "median_two_sorted": median_two_sorted,
}
