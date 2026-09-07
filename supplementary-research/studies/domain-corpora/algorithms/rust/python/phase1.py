"""Phase 1 — Dynamic Programming: idiomatic Python reference oracles.

Independent of the Rust primitive implementations under test
(the executable comparison). Each oracle is the
classic textbook formulation, written without reference to the
framework. This module exposes `ORACLES` (name -> fn); the shared
`oracles.py` dispatcher handles the JSON stdin/stdout protocol. One
oracle module per phase keeps the parallel build conflict-free.
"""

def climbing_stairs(n):
    if n < 0:
        n = 0
    a, b = 1, 1
    for _ in range(n):
        a, b = b, a + b
    return a


def house_robber(nums):
    take, skip = 0, 0
    for x in nums:
        take, skip = skip + x, max(take, skip)
    return max(take, skip)


def lis(nums):
    if not nums:
        return 0
    dp = [1] * len(nums)
    for i in range(len(nums)):
        for j in range(i):
            if nums[j] < nums[i]:
                dp[i] = max(dp[i], dp[j] + 1)
    return max(dp)


def coin_change(args):
    coins, amount = args
    INF = float("inf")
    dp = [0] + [INF] * amount
    for v in range(1, amount + 1):
        for c in coins:
            if 0 < c <= v and dp[v - c] + 1 < dp[v]:
                dp[v] = dp[v - c] + 1
    return -1 if dp[amount] == INF else dp[amount]


def word_break(args):
    s, words = args
    wordset = set(words)
    n = len(s)
    dp = [False] * (n + 1)
    dp[0] = True
    for i in range(1, n + 1):
        for j in range(i):
            if dp[j] and s[j:i] in wordset:
                dp[i] = True
                break
    return dp[n]


def unique_paths(args):
    m, n = args
    m = max(m, 1)
    n = max(n, 1)
    dp = [[1] * n for _ in range(m)]
    for i in range(1, m):
        for j in range(1, n):
            dp[i][j] = dp[i - 1][j] + dp[i][j - 1]
    return dp[m - 1][n - 1]


def lcs(args):
    a, b = args
    dp = [[0] * (len(b) + 1) for _ in range(len(a) + 1)]
    for i in range(1, len(a) + 1):
        for j in range(1, len(b) + 1):
            if a[i - 1] == b[j - 1]:
                dp[i][j] = dp[i - 1][j - 1] + 1
            else:
                dp[i][j] = max(dp[i - 1][j], dp[i][j - 1])
    return dp[len(a)][len(b)]


def edit_distance(args):
    a, b = args
    dp = [[0] * (len(b) + 1) for _ in range(len(a) + 1)]
    for i in range(len(a) + 1):
        dp[i][0] = i
    for j in range(len(b) + 1):
        dp[0][j] = j
    for i in range(1, len(a) + 1):
        for j in range(1, len(b) + 1):
            if a[i - 1] == b[j - 1]:
                dp[i][j] = dp[i - 1][j - 1]
            else:
                dp[i][j] = 1 + min(dp[i - 1][j], dp[i][j - 1], dp[i - 1][j - 1])
    return dp[len(a)][len(b)]


def knapsack_01(args):
    w, val, cap = args
    n = len(w)
    dp = [[0] * (cap + 1) for _ in range(n + 1)]
    for i in range(1, n + 1):
        for c in range(cap + 1):
            dp[i][c] = dp[i - 1][c]
            if w[i - 1] <= c:
                dp[i][c] = max(dp[i][c], dp[i - 1][c - w[i - 1]] + val[i - 1])
    return dp[n][cap]


def lps(s):
    n = len(s)
    if n == 0:
        return 0
    dp = [[0] * n for _ in range(n)]
    for i in range(n):
        dp[i][i] = 1
    for length in range(2, n + 1):
        for i in range(0, n - length + 1):
            j = i + length - 1
            if s[i] == s[j]:
                dp[i][j] = 2 + (dp[i + 1][j - 1] if length > 2 else 0)
            else:
                dp[i][j] = max(dp[i + 1][j], dp[i][j - 1])
    return dp[0][n - 1]


ORACLES = {
    "climbing_stairs": climbing_stairs,
    "house_robber": house_robber,
    "lis": lis,
    "coin_change": coin_change,
    "word_break": word_break,
    "unique_paths": unique_paths,
    "lcs": lcs,
    "edit_distance": edit_distance,
    "knapsack_01": knapsack_01,
    "lps": lps,
}
