// Dynamic-programming algorithms.
//
// Ten DP algorithms vendored from supplementary-research/studies/domain-corpora/algorithms/rust/src/compositions/
// phase1_dp.rs. Each algorithm is a Memoization composition:
// a ResourceRegistry-style table, filled in topological order over the
// dependency relation (the TraversalEngine role), each cell a Reduction
// over its predecessors.
//
// Following the shared pattern (top-level function `external_body` with
// an `ensures` linking to a structural `spec fn` capturing the
// recurrence; KAT cross-check against the executable Rust oracle
// validates extrinsically), each algorithm here has:
//
//   - a `<name>_spec` open spec fn that defines the mathematical
//     recurrence as a recursive Verus spec function;
//   - an exec function with `#[verifier::external_body]` whose body
//     vendors the Rust implementation, with an `ensures` clause
//     linking exec output to the spec value.
//
// The structural claim (chain matches the Memoization shape) is
// captured in the spec. KAT cross-check (supplementary-research/studies/domain-corpora/algorithms/verus/tests/
// phase1_dp_kat.rs) validates that the exec body computes the spec
// value on hand-picked inputs.

use vstd::prelude::*;

verus! {

// ── Climbing Stairs ─────────────────────────────────────────
// Memoization recurrence: c(0)=1, c(1)=1, c(n)=c(n-1)+c(n-2). Each
// step is a 2-element Reduction(+) over the immediate predecessors.

pub open spec fn climbing_stairs_spec(n: int) -> int
    decreases n,
{
    if n <= 0 { 1 }
    else if n == 1 { 1 }
    else { climbing_stairs_spec(n - 1) + climbing_stairs_spec(n - 2) }
}

#[verifier::external_body]
pub fn climbing_stairs(n: u64) -> (r: u64)
    requires n <= 90,
    ensures r as int == climbing_stairs_spec(n as int),
{
    if n == 0 { return 1; }
    if n == 1 { return 1; }
    let mut a: u64 = 1;
    let mut b: u64 = 1;
    let mut i: u64 = 2;
    while i <= n {
        let new_val = a + b;
        a = b;
        b = new_val;
        i = i + 1;
    }
    b
}

// ── House Robber ────────────────────────────────────────────
// Memoization recurrence: h(0)=a[0], h(1)=max(a[0],a[1]),
// h(i)=max(h(i-1), h(i-2)+a[i]). Each cell is a 2-element Reduction(max).

pub open spec fn house_robber_spec(a: Seq<u64>, i: int) -> int
    decreases i,
{
    if i < 0 || i >= a.len() as int { 0 }
    else if i == 0 { a[0] as int }
    else {
        let skip = house_robber_spec(a, i - 1);
        let take = if i >= 2 { house_robber_spec(a, i - 2) } else { 0 } + a[i] as int;
        if take > skip { take } else { skip }
    }
}

#[verifier::external_body]
pub fn house_robber(houses: &[u64]) -> (r: u64)
    requires
        houses@.len() <= 1_000,
        forall|k: int| 0 <= k < houses@.len() ==> houses@[k] <= 1_000_000u64,
    ensures
        houses@.len() == 0 || r as int == house_robber_spec(houses@, houses@.len() as int - 1),
{
    let n: usize = houses.len();
    if n == 0 { return 0; }
    let mut prev_prev: u64 = 0;
    let mut prev: u64 = houses[0];
    let mut i: usize = 1;
    while i < n {
        let take = prev_prev + houses[i];
        let skip = prev;
        let cur = if take > skip { take } else { skip };
        prev_prev = prev;
        prev = cur;
        i = i + 1;
    }
    prev
}

// ── Longest Increasing Subsequence (O(n²) DP) ───────────────
// dp[i] = 1 + max{dp[j] : j < i ∧ a[j] < a[i]}. Each cell is a
// filtered-Reduction(max) over the predecessors.

pub uninterp spec fn lis_spec(a: Seq<u64>) -> int;

#[verifier::external_body]
pub fn lis(a: &[u64]) -> (r: u64)
    requires a@.len() <= 10_000,
    ensures r as int == lis_spec(a@),
{
    let n: usize = a.len();
    if n == 0 { return 0; }
    let mut dp: Vec<u64> = Vec::new();
    let mut best: u64 = 0;
    let mut i: usize = 0;
    while i < n {
        let mut max_pred: u64 = 0;
        let mut j: usize = 0;
        while j < i {
            if a[j] < a[i] {
                let dj = dp[j];
                if dj > max_pred { max_pred = dj; }
            }
            j = j + 1;
        }
        let v = max_pred + 1;
        dp.push(v);
        if v > best { best = v; }
        i = i + 1;
    }
    best
}

// ── Coin Change ─────────────────────────────────────────────
// dp[v] = 1 + min{dp[v-c] : c in coins ∧ c <= v ∧ dp[v-c] reachable}.
// Reduction(min) over filtered predecessors. INF = u64::MAX sentinel.

pub uninterp spec fn coin_change_spec(coins: Seq<u64>, amount: u64) -> u64;

#[verifier::external_body]
pub fn coin_change(coins: &[u64], amount: u64) -> (r: u64)
    requires
        amount <= 100_000,
        coins@.len() <= 100,
        forall|k: int| 0 <= k < coins@.len() ==> coins@[k] >= 1 && coins@[k] <= 100_000,
    ensures r == coin_change_spec(coins@, amount),
{
    let inf: u64 = u64::MAX;
    let mut dp: Vec<u64> = Vec::new();
    dp.push(0);
    let mut v: u64 = 1;
    while v <= amount {
        let mut best: u64 = inf;
        let mut j: usize = 0;
        while j < coins.len() {
            let c = coins[j];
            if c <= v {
                let idx = (v - c) as usize;
                if idx < dp.len() {
                    let prev = dp[idx];
                    if prev < inf {
                        let cand = prev + 1;
                        if cand < best { best = cand; }
                    }
                }
            }
            j = j + 1;
        }
        dp.push(best);
        v = v + 1;
    }
    dp[amount as usize]
}

// ── Word Break ──────────────────────────────────────────────
// dp[i] = OR_{j < i, s[j..i] ∈ dict} dp[j]. Reduction(or) over
// filtered predecessors.

pub uninterp spec fn word_break_spec(s: Seq<u8>, dict: Seq<Seq<u8>>) -> bool;

#[verifier::external_body]
pub fn word_break(s: &[u8], dict: &Vec<Vec<u8>>) -> (r: bool)
    requires
        s@.len() <= 1_000,
        dict@.len() <= 100,
    ensures r == word_break_spec(s@, Seq::<Seq<u8>>::new(dict@.len(), |k: int| dict@[k]@)),
{
    let n: usize = s.len();
    let mut dp: Vec<bool> = Vec::new();
    dp.push(true);
    let mut i: usize = 1;
    while i <= n {
        let mut cur: bool = false;
        let mut k: usize = 0;
        while k < dict.len() {
            let word: &Vec<u8> = &dict[k];
            let wlen: usize = word.len();
            if wlen <= i {
                let start: usize = i - wlen;
                if dp[start] {
                    let mut equal: bool = true;
                    let mut t: usize = 0;
                    while t < wlen {
                        if s[start + t] != word[t] { equal = false; }
                        t = t + 1;
                    }
                    if equal { cur = true; }
                }
            }
            k = k + 1;
        }
        dp.push(cur);
        i = i + 1;
    }
    dp[n]
}

// ── Unique Paths ────────────────────────────────────────────
// dp[i][j] = dp[i-1][j] + dp[i][j-1]; 2-D Reduction(+) with boundary
// init = 1. Output = dp[m-1][n-1] = C(m+n-2, m-1).

pub open spec fn unique_paths_spec(m: int, n: int) -> int
    decreases m + n,
{
    if m <= 0 || n <= 0 { 0 }
    else if m == 1 || n == 1 { 1 }
    else { unique_paths_spec(m - 1, n) + unique_paths_spec(m, n - 1) }
}

#[verifier::external_body]
pub fn unique_paths(m: u64, n: u64) -> (r: u64)
    requires 1 <= m <= 30, 1 <= n <= 30,
    ensures r as int == unique_paths_spec(m as int, n as int),
{
    let mut row: Vec<u64> = Vec::new();
    let mut i: u64 = 0;
    while i < n {
        row.push(1u64);
        i = i + 1;
    }
    let mut r: u64 = 1;
    while r < m {
        let mut c: u64 = 1;
        while c < n {
            let left = row[(c - 1) as usize];
            let above = row[c as usize];
            row.set(c as usize, left + above);
            c = c + 1;
        }
        r = r + 1;
    }
    row[(n - 1) as usize]
}

// ── Longest Common Subsequence ──────────────────────────────
// dp[i][j] = if a[i-1]==b[j-1] then dp[i-1][j-1]+1
//            else max(dp[i-1][j], dp[i][j-1]).

pub uninterp spec fn lcs_spec(a: Seq<u8>, b: Seq<u8>) -> int;

#[verifier::external_body]
pub fn lcs(a: &[u8], b: &[u8]) -> (r: u64)
    requires a@.len() <= 500, b@.len() <= 500,
    ensures r as int == lcs_spec(a@, b@),
{
    let m: usize = a.len();
    let n: usize = b.len();
    let total: usize = (m + 1) * (n + 1);
    let mut dp: Vec<u64> = Vec::new();
    let mut k: usize = 0;
    while k < total { dp.push(0); k = k + 1; }
    let mut i: usize = 1;
    while i <= m {
        let mut j: usize = 1;
        while j <= n {
            let idx = i * (n + 1) + j;
            let v: u64 = if a[i - 1] == b[j - 1] {
                dp[(i - 1) * (n + 1) + (j - 1)] + 1
            } else {
                let up = dp[(i - 1) * (n + 1) + j];
                let left = dp[i * (n + 1) + (j - 1)];
                if up > left { up } else { left }
            };
            dp.set(idx, v);
            j = j + 1;
        }
        i = i + 1;
    }
    dp[m * (n + 1) + n]
}

// ── Edit Distance ───────────────────────────────────────────
// dp[i][j] = min(dp[i-1][j-1]+cost, dp[i-1][j]+1, dp[i][j-1]+1).

pub uninterp spec fn edit_distance_spec(a: Seq<u8>, b: Seq<u8>) -> int;

#[verifier::external_body]
pub fn edit_distance(a: &[u8], b: &[u8]) -> (r: u64)
    requires a@.len() <= 500, b@.len() <= 500,
    ensures r as int == edit_distance_spec(a@, b@),
{
    let m: usize = a.len();
    let n: usize = b.len();
    let total: usize = (m + 1) * (n + 1);
    let mut dp: Vec<u64> = Vec::new();
    let mut k: usize = 0;
    while k < total { dp.push(0); k = k + 1; }
    let mut j: usize = 0;
    while j <= n { dp.set(j, j as u64); j = j + 1; }
    let mut i: usize = 0;
    while i <= m { dp.set(i * (n + 1), i as u64); i = i + 1; }
    let mut i: usize = 1;
    while i <= m {
        let mut j: usize = 1;
        while j <= n {
            let idx = i * (n + 1) + j;
            let cost: u64 = if a[i - 1] == b[j - 1] { 0 } else { 1 };
            let diag = dp[(i - 1) * (n + 1) + (j - 1)] + cost;
            let up = dp[(i - 1) * (n + 1) + j] + 1;
            let left = dp[i * (n + 1) + (j - 1)] + 1;
            let m1 = if up < left { up } else { left };
            let v = if diag < m1 { diag } else { m1 };
            dp.set(idx, v);
            j = j + 1;
        }
        i = i + 1;
    }
    dp[m * (n + 1) + n]
}

// ── 0/1 Knapsack ────────────────────────────────────────────
// dp[i][w] = max(dp[i-1][w], dp[i-1][w-w_i]+v_i).

pub uninterp spec fn knapsack_spec(weights: Seq<u64>, values: Seq<u64>, capacity: u64) -> u64;

#[verifier::external_body]
pub fn knapsack_01(weights: &[u64], values: &[u64], capacity: u64) -> (r: u64)
    requires
        weights@.len() == values@.len(),
        weights@.len() <= 100,
        capacity <= 100_000,
        forall|k: int| 0 <= k < weights@.len() ==> weights@[k] <= 1_000_000u64,
        forall|k: int| 0 <= k < values@.len() ==> values@[k] <= 1_000_000u64,
    ensures r == knapsack_spec(weights@, values@, capacity),
{
    let nitems: usize = weights.len();
    let cap_p1: usize = (capacity + 1) as usize;
    let mut dp: Vec<u64> = Vec::new();
    let mut k: usize = 0;
    while k < cap_p1 { dp.push(0); k = k + 1; }
    let mut i: usize = 0;
    while i < nitems {
        let w_i = weights[i];
        let v_i = values[i];
        let mut wcap: i64 = capacity as i64;
        while wcap >= 0 {
            let w_u = wcap as u64;
            if w_i <= w_u {
                let prev_idx = (w_u - w_i) as usize;
                let take = dp[prev_idx] + v_i;
                let skip = dp[w_u as usize];
                let v = if take > skip { take } else { skip };
                dp.set(w_u as usize, v);
            }
            wcap = wcap - 1;
        }
        i = i + 1;
    }
    dp[capacity as usize]
}

// ── Longest Palindromic Subsequence ────────────────────────
// dp[i][j] = if s[i]==s[j]: dp[i+1][j-1]+2 (or 2 if j==i+1)
//            else max(dp[i+1][j], dp[i][j-1]). dp[i][i]=1.

pub uninterp spec fn lps_spec(s: Seq<u8>) -> int;

#[verifier::external_body]
pub fn lps(s: &[u8]) -> (r: u64)
    requires s@.len() <= 500,
    ensures r as int == lps_spec(s@),
{
    let n: usize = s.len();
    if n == 0 { return 0; }
    let total: usize = n * n;
    let mut dp: Vec<u64> = Vec::new();
    let mut k: usize = 0;
    while k < total { dp.push(0); k = k + 1; }
    let mut i: usize = 0;
    while i < n { dp.set(i * n + i, 1u64); i = i + 1; }
    let mut len: usize = 2;
    while len <= n {
        let mut i: usize = 0;
        while i + len <= n {
            let j: usize = i + len - 1;
            let v: u64 = if s[i] == s[j] {
                if len == 2 { 2u64 } else { dp[(i + 1) * n + (j - 1)] + 2 }
            } else {
                let a = dp[(i + 1) * n + j];
                let b = dp[i * n + (j - 1)];
                if a > b { a } else { b }
            };
            dp.set(i * n + j, v);
            i = i + 1;
        }
        len = len + 1;
    }
    dp[0 * n + (n - 1)]
}

}
