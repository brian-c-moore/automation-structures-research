// Stack & Binary-search algorithms.
//
// Ten algorithms vendored from supplementary-research/studies/domain-corpora/algorithms/rust/src/compositions/
// phase2_stack_bsearch.rs. Each algorithm uses the MonotonicStack
// composition, the Bisection primitive, or both.

use vstd::prelude::*;

verus! {

// ── Valid Parentheses (Stack) ───────────────────────────────
pub uninterp spec fn valid_parens_spec(s: Seq<u8>) -> bool;

#[verifier::external_body]
pub fn valid_parentheses(s: &[u8]) -> (r: bool)
    requires s@.len() <= 10_000,
    ensures r == valid_parens_spec(s@),
{
    let mut stack: Vec<u8> = Vec::new();
    let n = s.len();
    let mut i: usize = 0;
    while i < n {
        let c = s[i];
        if c == b'(' || c == b'[' || c == b'{' {
            stack.push(c);
        } else {
            if stack.is_empty() { return false; }
            let top = stack[stack.len() - 1];
            let ok = (c == b')' && top == b'(')
                || (c == b']' && top == b'[')
                || (c == b'}' && top == b'{');
            if !ok { return false; }
            stack.pop();
        }
        i = i + 1;
    }
    stack.is_empty()
}

// ── Min Stack (Stack with O(1) min) ─────────────────────────
// Functional form: given a sequence of operations encoded as (op, value)
// pairs (op=0:push value, op=1:pop, op=2:get_min returns top of mins),
// return the sequence of get_min results.
pub uninterp spec fn min_stack_spec(ops: Seq<u8>, vals: Seq<i64>) -> Seq<i64>;

#[verifier::external_body]
pub fn min_stack(ops: &[u8], vals: &[i64]) -> (r: Vec<i64>)
    requires
        ops@.len() == vals@.len(),
        ops@.len() <= 10_000,
    ensures r@ == min_stack_spec(ops@, vals@),
{
    let mut stack: Vec<i64> = Vec::new();
    let mut mins: Vec<i64> = Vec::new();
    let mut out: Vec<i64> = Vec::new();
    let n = ops.len();
    let mut i: usize = 0;
    while i < n {
        let op = ops[i];
        let v = vals[i];
        if op == 0 {
            stack.push(v);
            let m = if mins.is_empty() { v } else {
                let last = mins[mins.len() - 1];
                if v < last { v } else { last }
            };
            mins.push(m);
        } else if op == 1 {
            if !stack.is_empty() {
                stack.pop();
                mins.pop();
            }
        } else if op == 2 {
            if !mins.is_empty() {
                out.push(mins[mins.len() - 1]);
            }
        }
        i = i + 1;
    }
    out
}

// ── Evaluate Reverse Polish Notation ────────────────────────
// Tokens: positive numbers + 4 ops (encoded as i64 sentinels:
// i64::MIN..MIN+3 for +, -, *, /). Returns final value.
pub uninterp spec fn eval_rpn_spec(tokens: Seq<i64>) -> i64;

#[verifier::external_body]
pub fn eval_rpn(tokens: &[i64]) -> (r: i64)
    requires tokens@.len() <= 10_000,
    ensures r == eval_rpn_spec(tokens@),
{
    let op_add = i64::MIN;
    let op_sub = i64::MIN + 1;
    let op_mul = i64::MIN + 2;
    let op_div = i64::MIN + 3;
    let mut stack: Vec<i64> = Vec::new();
    let n = tokens.len();
    let mut i: usize = 0;
    while i < n {
        let t = tokens[i];
        if t == op_add || t == op_sub || t == op_mul || t == op_div {
            if stack.len() >= 2 {
                let b = stack[stack.len() - 1]; stack.pop();
                let a = stack[stack.len() - 1]; stack.pop();
                let v = if t == op_add { a.wrapping_add(b) }
                    else if t == op_sub { a.wrapping_sub(b) }
                    else if t == op_mul { a.wrapping_mul(b) }
                    else { if b != 0 { a / b } else { 0 } };
                stack.push(v);
            }
        } else {
            stack.push(t);
        }
        i = i + 1;
    }
    if stack.is_empty() { 0 } else { stack[stack.len() - 1] }
}

// ── Daily Temperatures (Monotonic Stack) ────────────────────
pub uninterp spec fn daily_temperatures_spec(t: Seq<i64>) -> Seq<u64>;

#[verifier::external_body]
pub fn daily_temperatures(t: &[i64]) -> (r: Vec<u64>)
    requires t@.len() <= 10_000,
    ensures r@ == daily_temperatures_spec(t@),
{
    let n = t.len();
    let mut out: Vec<u64> = Vec::new();
    let mut i: usize = 0;
    while i < n { out.push(0); i = i + 1; }
    let mut stack: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        while !stack.is_empty() && t[stack[stack.len() - 1]] < t[i] {
            let k = stack[stack.len() - 1];
            stack.pop();
            out.set(k, (i - k) as u64);
        }
        stack.push(i);
        i = i + 1;
    }
    out
}

// ── Largest Rectangle in Histogram (Monotonic Stack) ────────
pub uninterp spec fn largest_rect_spec(h: Seq<u64>) -> u64;

#[verifier::external_body]
pub fn largest_rect_histogram(heights: &[u64]) -> (r: u64)
    requires
        heights@.len() <= 10_000,
        forall|k: int| 0 <= k < heights@.len() ==> heights@[k] <= 1_000_000_000u64,
    ensures r == largest_rect_spec(heights@),
{
    let n = heights.len();
    let mut stack: Vec<usize> = Vec::new();
    let mut best: u64 = 0;
    let mut i: usize = 0;
    while i <= n {
        let cur_h: u64 = if i == n { 0 } else { heights[i] };
        while !stack.is_empty() && heights[stack[stack.len() - 1]] > cur_h {
            let top_idx = stack[stack.len() - 1];
            let top_h = heights[top_idx];
            stack.pop();
            let left = if stack.is_empty() { 0 } else { stack[stack.len() - 1] + 1 };
            let width = (i - left) as u64;
            let area = top_h * width;
            if area > best { best = area; }
        }
        stack.push(i);
        i = i + 1;
    }
    best
}

// ── Binary Search (Bisection primitive) ─────────────────────
pub uninterp spec fn bsearch_spec(a: Seq<i64>, target: i64) -> i64;

#[verifier::external_body]
pub fn binary_search(a: &[i64], target: i64) -> (r: i64)
    requires a@.len() <= 1_000_000,
    ensures r == bsearch_spec(a@, target),
{
    let n = a.len();
    let mut lo: i64 = 0;
    let mut hi: i64 = n as i64;
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        let v = a[mid as usize];
        if v == target { return mid; }
        else if v < target { lo = mid + 1; }
        else { hi = mid; }
    }
    -1
}

// ── Search in Rotated Sorted Array ──────────────────────────
pub uninterp spec fn search_rotated_spec(a: Seq<i64>, target: i64) -> i64;

#[verifier::external_body]
pub fn search_rotated(a: &[i64], target: i64) -> (r: i64)
    requires a@.len() <= 1_000_000,
    ensures r == search_rotated_spec(a@, target),
{
    let n = a.len();
    if n == 0 { return -1; }
    let mut lo: i64 = 0;
    let mut hi: i64 = (n as i64) - 1;
    while lo <= hi {
        let mid = lo + (hi - lo) / 2;
        let m_val = a[mid as usize];
        if m_val == target { return mid; }
        if a[lo as usize] <= m_val {
            if a[lo as usize] <= target && target < m_val {
                hi = mid - 1;
            } else { lo = mid + 1; }
        } else {
            if m_val < target && target <= a[hi as usize] {
                lo = mid + 1;
            } else { hi = mid - 1; }
        }
    }
    -1
}

// ── Find Minimum in Rotated Sorted Array ────────────────────
pub uninterp spec fn find_min_rotated_spec(a: Seq<i64>) -> i64;

#[verifier::external_body]
pub fn find_min_rotated(a: &[i64]) -> (r: i64)
    requires a@.len() >= 1, a@.len() <= 1_000_000,
    ensures r == find_min_rotated_spec(a@),
{
    let n = a.len();
    let mut lo: usize = 0;
    let mut hi: usize = n - 1;
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if a[mid] > a[hi] { lo = mid + 1; } else { hi = mid; }
    }
    a[lo]
}

// ── Koko Eating Bananas (Binary search on answer) ───────────
pub uninterp spec fn koko_spec(piles: Seq<u64>, h: u64) -> u64;

#[verifier::external_body]
pub fn koko_bananas(piles: &[u64], h: u64) -> (r: u64)
    requires
        piles@.len() >= 1,
        piles@.len() <= 10_000,
        h >= piles@.len() as u64,
        forall|k: int| 0 <= k < piles@.len() ==> piles@[k] >= 1 && piles@[k] <= 1_000_000_000u64,
    ensures r == koko_spec(piles@, h),
{
    let n = piles.len();
    let mut lo: u64 = 1;
    let mut hi: u64 = 0;
    let mut i: usize = 0;
    while i < n { if piles[i] > hi { hi = piles[i]; } i = i + 1; }
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        // Hours required at speed `mid`.
        let mut hours: u64 = 0;
        let mut overflow: bool = false;
        let mut i: usize = 0;
        while i < n {
            let p = piles[i];
            let used = (p + mid - 1) / mid;
            hours = hours + used;
            if hours > h { overflow = true; }
            i = i + 1;
        }
        if overflow { lo = mid + 1; } else { hi = mid; }
    }
    lo
}

// ── Median of Two Sorted Arrays ────────────────────────────
// Returns median × 2 (to keep result integer-valued).
pub uninterp spec fn median_two_sorted_spec(a: Seq<i64>, b: Seq<i64>) -> i64;

#[verifier::external_body]
pub fn median_two_sorted(a: &[i64], b: &[i64]) -> (r: i64)
    requires
        a@.len() + b@.len() >= 1,
        a@.len() <= 100_000,
        b@.len() <= 100_000,
    ensures r == median_two_sorted_spec(a@, b@),
{
    // Reference fallback: merge-then-pick. O(n+m).
    let n = a.len();
    let m = b.len();
    let mut merged: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    let mut j: usize = 0;
    while i < n || j < m {
        if i < n && (j >= m || a[i] <= b[j]) {
            merged.push(a[i]); i = i + 1;
        } else {
            merged.push(b[j]); j = j + 1;
        }
    }
    let len = merged.len();
    if len == 0 { return 0; }
    if len % 2 == 1 { return merged[len / 2] * 2; }
    let lo = merged[len / 2 - 1];
    let hi = merged[len / 2];
    lo + hi
}

}
