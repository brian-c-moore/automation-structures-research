// Greedy, Intervals, Math & Geometry, Bit Manipulation. Eighteen algorithms.

use vstd::prelude::*;

verus! {

// ── Maximum Subarray (Kadane's) ─────────────────────────────
pub uninterp spec fn maximum_subarray_spec(a: Seq<i64>) -> i64;

#[verifier::external_body]
pub fn maximum_subarray(a: &[i64]) -> (r: i64)
    requires
        a@.len() >= 1,
        a@.len() <= 100_000,
        forall|i: int| 0 <= i < a@.len() ==> a@[i] >= -1_000_000 && a@[i] <= 1_000_000,
    ensures r == maximum_subarray_spec(a@),
{
    let mut best = a[0];
    let mut cur = a[0];
    let n = a.len();
    let mut i: usize = 1;
    while i < n {
        let v = a[i];
        cur = if cur + v > v { cur + v } else { v };
        if cur > best { best = cur; }
        i = i + 1;
    }
    best
}

// ── Jump Game ───────────────────────────────────────────────
pub uninterp spec fn jump_game_spec(a: Seq<u64>) -> bool;

#[verifier::external_body]
pub fn jump_game(a: &[u64]) -> (r: bool)
    requires
        a@.len() <= 100_000,
        forall|i: int| 0 <= i < a@.len() ==> a@[i] <= 100_000,
    ensures r == jump_game_spec(a@),
{
    let n = a.len();
    if n == 0 { return true; }
    let mut reach: u64 = 0;
    let mut i: usize = 0;
    while i < n {
        if i as u64 > reach { return false; }
        let v = (i as u64) + a[i];
        if v > reach { reach = v; }
        i = i + 1;
    }
    true
}

// ── Gas Station ─────────────────────────────────────────────
pub uninterp spec fn gas_station_spec(gas: Seq<i64>, cost: Seq<i64>) -> i64;

#[verifier::external_body]
pub fn gas_station(gas: &[i64], cost: &[i64]) -> (r: i64)
    requires
        gas@.len() == cost@.len(),
        gas@.len() <= 100_000,
        forall|i: int| 0 <= i < gas@.len() ==> gas@[i] >= 0 && gas@[i] <= 1_000_000,
        forall|i: int| 0 <= i < cost@.len() ==> cost@[i] >= 0 && cost@[i] <= 1_000_000,
    ensures r == gas_station_spec(gas@, cost@),
{
    let mut total: i64 = 0;
    let mut tank: i64 = 0;
    let mut start: i64 = 0;
    let n = gas.len();
    let mut i: usize = 0;
    while i < n {
        let diff = gas[i] - cost[i];
        total = total + diff;
        tank = tank + diff;
        if tank < 0 { start = (i + 1) as i64; tank = 0; }
        i = i + 1;
    }
    if total < 0 { -1 } else { start }
}

// ── Hand of Straights ───────────────────────────────────────
pub uninterp spec fn hand_of_straights_spec(hand: Seq<i64>, group_size: usize) -> bool;

#[verifier::external_body]
pub fn hand_of_straights(hand: &[i64], group_size: usize) -> (r: bool)
    requires
        hand@.len() <= 10_000,
        group_size >= 1,
    ensures r == hand_of_straights_spec(hand@, group_size),
{
    let n = hand.len();
    if n % group_size != 0 { return false; }
    let mut sorted: Vec<i64> = hand.to_vec();
    sorted.sort();
    // count[v] = remaining. Use parallel vectors keys/counts.
    let mut keys: Vec<i64> = Vec::new();
    let mut counts: Vec<u64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        let mut j = i;
        while j < n && sorted[j] == sorted[i] { j = j + 1; }
        keys.push(sorted[i]);
        counts.push((j - i) as u64);
        i = j;
    }
    let mut idx: usize = 0;
    while idx < keys.len() {
        while idx < keys.len() && counts[idx] == 0 { idx = idx + 1; }
        if idx >= keys.len() { break; }
        let cnt = counts[idx];
        let mut g: usize = 0;
        while g < group_size {
            let want = keys[idx] + (g as i64);
            // Find want in keys[idx..].
            let mut k = idx;
            while k < keys.len() && keys[k] != want { k = k + 1; }
            if k >= keys.len() || counts[k] < cnt { return false; }
            counts.set(k, counts[k] - cnt);
            g = g + 1;
        }
    }
    true
}

// ── Merge Intervals ─────────────────────────────────────────
// Input parallel arrays starts/ends; returns (starts, ends).
pub uninterp spec fn merge_intervals_spec(starts: Seq<i64>, ends: Seq<i64>) -> (Seq<i64>, Seq<i64>);

#[verifier::external_body]
pub fn merge_intervals(starts: &[i64], ends: &[i64]) -> (r: (Vec<i64>, Vec<i64>))
    requires
        starts@.len() == ends@.len(),
        starts@.len() <= 10_000,
    ensures (r.0@, r.1@) == merge_intervals_spec(starts@, ends@),
{
    let n = starts.len();
    if n == 0 { return (Vec::new(), Vec::new()); }
    // Pair + sort by start.
    let mut idx: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < n { idx.push(i); i = i + 1; }
    // Selection sort indices by starts[idx[i]].
    let mut i: usize = 0;
    while i < n {
        let mut best = i;
        let mut j = i + 1;
        while j < n {
            if starts[idx[j]] < starts[idx[best]] { best = j; }
            j = j + 1;
        }
        let t = idx[i]; idx.set(i, idx[best]); idx.set(best, t);
        i = i + 1;
    }
    let mut out_s: Vec<i64> = Vec::new();
    let mut out_e: Vec<i64> = Vec::new();
    out_s.push(starts[idx[0]]);
    out_e.push(ends[idx[0]]);
    let mut i: usize = 1;
    while i < n {
        let s = starts[idx[i]]; let e = ends[idx[i]];
        let last_e = out_e[out_e.len() - 1];
        if s <= last_e {
            let new_e = if e > last_e { e } else { last_e };
            let l = out_e.len() - 1;
            out_e.set(l, new_e);
        } else {
            out_s.push(s); out_e.push(e);
        }
        i = i + 1;
    }
    (out_s, out_e)
}

// ── Insert Interval ─────────────────────────────────────────
pub uninterp spec fn insert_interval_spec(
    starts: Seq<i64>, ends: Seq<i64>, ns: i64, ne: i64,
) -> (Seq<i64>, Seq<i64>);

#[verifier::external_body]
pub fn insert_interval(starts: &[i64], ends: &[i64], ns: i64, ne: i64) -> (r: (Vec<i64>, Vec<i64>))
    requires
        starts@.len() == ends@.len(),
        starts@.len() <= 10_000,
    ensures (r.0@, r.1@) == insert_interval_spec(starts@, ends@, ns, ne),
{
    let n = starts.len();
    let mut out_s: Vec<i64> = Vec::new();
    let mut out_e: Vec<i64> = Vec::new();
    let mut cur_s = ns;
    let mut cur_e = ne;
    let mut placed = false;
    let mut i: usize = 0;
    while i < n {
        let s = starts[i]; let e = ends[i];
        if e < cur_s {
            out_s.push(s); out_e.push(e);
        } else if s > cur_e {
            if !placed { out_s.push(cur_s); out_e.push(cur_e); placed = true; }
            out_s.push(s); out_e.push(e);
        } else {
            if s < cur_s { cur_s = s; }
            if e > cur_e { cur_e = e; }
        }
        i = i + 1;
    }
    if !placed { out_s.push(cur_s); out_e.push(cur_e); }
    (out_s, out_e)
}

// ── Non-Overlapping Intervals (returns removals needed) ─────
pub uninterp spec fn non_overlapping_intervals_spec(starts: Seq<i64>, ends: Seq<i64>) -> u64;

#[verifier::external_body]
pub fn non_overlapping_intervals(starts: &[i64], ends: &[i64]) -> (r: u64)
    requires
        starts@.len() == ends@.len(),
        starts@.len() <= 10_000,
    ensures r == non_overlapping_intervals_spec(starts@, ends@),
{
    let n = starts.len();
    if n == 0 { return 0; }
    let mut idx: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < n { idx.push(i); i = i + 1; }
    // Sort by ends ascending.
    let mut i: usize = 0;
    while i < n {
        let mut best = i;
        let mut j = i + 1;
        while j < n {
            if ends[idx[j]] < ends[idx[best]] { best = j; }
            j = j + 1;
        }
        let t = idx[i]; idx.set(i, idx[best]); idx.set(best, t);
        i = i + 1;
    }
    let mut kept: u64 = 1;
    let mut prev_end: i64 = ends[idx[0]];
    let mut i: usize = 1;
    while i < n {
        if starts[idx[i]] >= prev_end {
            kept = kept + 1; prev_end = ends[idx[i]];
        }
        i = i + 1;
    }
    (n as u64) - kept
}

// ── Meeting Rooms II (min rooms needed) ─────────────────────
pub uninterp spec fn meeting_rooms_ii_spec(starts: Seq<i64>, ends: Seq<i64>) -> u64;

#[verifier::external_body]
pub fn meeting_rooms_ii(starts: &[i64], ends: &[i64]) -> (r: u64)
    requires
        starts@.len() == ends@.len(),
        starts@.len() <= 10_000,
    ensures r == meeting_rooms_ii_spec(starts@, ends@),
{
    let n = starts.len();
    let mut s_sorted: Vec<i64> = starts.to_vec();
    let mut e_sorted: Vec<i64> = ends.to_vec();
    s_sorted.sort();
    e_sorted.sort();
    let mut rooms: u64 = 0;
    let mut max_rooms: u64 = 0;
    let mut i: usize = 0;
    let mut j: usize = 0;
    while i < n {
        if j < n && s_sorted[i] >= e_sorted[j] {
            rooms = rooms - 1;
            j = j + 1;
        }
        rooms = rooms + 1;
        if rooms > max_rooms { max_rooms = rooms; }
        i = i + 1;
    }
    max_rooms
}

// ── Rotate Image (in-place 90° clockwise) ───────────────────
pub uninterp spec fn rotate_image_spec(n: usize, mat: Seq<i64>) -> Seq<i64>;

#[verifier::external_body]
pub fn rotate_image(n: usize, mat: &[i64]) -> (r: Vec<i64>)
    requires
        mat@.len() == n * n,
        n <= 100,
    ensures r@ == rotate_image_spec(n, mat@),
{
    let mut out: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n * n { out.push(0); i = i + 1; }
    let mut i: usize = 0;
    while i < n {
        let mut j: usize = 0;
        while j < n {
            out.set(j * n + (n - 1 - i), mat[i * n + j]);
            j = j + 1;
        }
        i = i + 1;
    }
    out
}

// ── Spiral Matrix ──────────────────────────────────────────
pub uninterp spec fn spiral_matrix_spec(rows: usize, cols: usize, mat: Seq<i64>) -> Seq<i64>;

#[verifier::external_body]
pub fn spiral_matrix(rows: usize, cols: usize, mat: &[i64]) -> (r: Vec<i64>)
    requires
        mat@.len() == rows * cols,
        rows <= 100, cols <= 100,
    ensures r@ == spiral_matrix_spec(rows, cols, mat@),
{
    let mut out: Vec<i64> = Vec::new();
    if rows == 0 || cols == 0 { return out; }
    let mut top: i64 = 0;
    let mut bottom: i64 = (rows as i64) - 1;
    let mut left: i64 = 0;
    let mut right: i64 = (cols as i64) - 1;
    while top <= bottom && left <= right {
        let mut c: i64 = left;
        while c <= right { out.push(mat[(top as usize) * cols + (c as usize)]); c = c + 1; }
        top = top + 1;
        let mut r_: i64 = top;
        while r_ <= bottom { out.push(mat[(r_ as usize) * cols + (right as usize)]); r_ = r_ + 1; }
        right = right - 1;
        if top <= bottom {
            let mut c: i64 = right;
            while c >= left { out.push(mat[(bottom as usize) * cols + (c as usize)]); c = c - 1; }
            bottom = bottom - 1;
        }
        if left <= right {
            let mut r_: i64 = bottom;
            while r_ >= top { out.push(mat[(r_ as usize) * cols + (left as usize)]); r_ = r_ - 1; }
            left = left + 1;
        }
    }
    out
}

// ── Set Matrix Zeroes ──────────────────────────────────────
pub uninterp spec fn set_matrix_zeroes_spec(rows: usize, cols: usize, mat: Seq<i64>) -> Seq<i64>;

#[verifier::external_body]
pub fn set_matrix_zeroes(rows: usize, cols: usize, mat: &[i64]) -> (r: Vec<i64>)
    requires
        mat@.len() == rows * cols,
        rows <= 200, cols <= 200,
    ensures r@ == set_matrix_zeroes_spec(rows, cols, mat@),
{
    let mut zero_row: Vec<bool> = Vec::new();
    let mut zero_col: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < rows { zero_row.push(false); i = i + 1; }
    let mut i: usize = 0;
    while i < cols { zero_col.push(false); i = i + 1; }
    let mut r: usize = 0;
    while r < rows {
        let mut c: usize = 0;
        while c < cols {
            if mat[r * cols + c] == 0 { zero_row.set(r, true); zero_col.set(c, true); }
            c = c + 1;
        }
        r = r + 1;
    }
    let mut out: Vec<i64> = mat.to_vec();
    let mut r: usize = 0;
    while r < rows {
        let mut c: usize = 0;
        while c < cols {
            if zero_row[r] || zero_col[c] { out.set(r * cols + c, 0); }
            c = c + 1;
        }
        r = r + 1;
    }
    out
}

// ── Pow(x, n) — integer base, n possibly negative ──────────
// Return: base^n if n >= 0; 0 if n < 0 (treat as invalid for integers).
pub uninterp spec fn pow_xn_spec(base: i64, n: i64) -> i64;

#[verifier::external_body]
pub fn pow_xn(base: i64, n: i64) -> (r: i64)
    requires n >= 0, n <= 60,
    ensures r == pow_xn_spec(base, n),
{
    let mut result: i64 = 1;
    let mut acc = base;
    let mut e = n;
    while e > 0 {
        if e & 1 == 1 { result = result.wrapping_mul(acc); }
        acc = acc.wrapping_mul(acc);
        e = e >> 1;
    }
    result
}

// ── Happy Number ───────────────────────────────────────────
pub uninterp spec fn happy_number_spec(n: u64) -> bool;

#[verifier::external_body]
pub fn happy_number(n: u64) -> (r: bool)
    requires n <= 1_000_000_000,
    ensures r == happy_number_spec(n),
{
    fn sq_digits(x: u64) -> u64 {
        let mut s: u64 = 0;
        let mut y = x;
        while y > 0 {
            let d = y % 10;
            s = s + d * d;
            y = y / 10;
        }
        s
    }
    let mut slow = n;
    let mut fast = n;
    loop {
        slow = sq_digits(slow);
        fast = sq_digits(sq_digits(fast));
        if slow == 1 || fast == 1 { return true; }
        if slow == fast { return false; }
    }
}

// ── Hamming Weight (count set bits) ────────────────────────
pub open spec fn hamming_weight_spec(n: u64) -> int
    decreases n,
{
    if n == 0 { 0 } else { (n & 1) as int + hamming_weight_spec(n / 2) }
}

#[verifier::external_body]
pub fn hamming_weight(n: u64) -> (r: u64)
    ensures r as int == hamming_weight_spec(n),
{
    let mut count: u64 = 0;
    let mut x = n;
    while x > 0 { count = count + (x & 1); x = x >> 1; }
    count
}

// ── Single Number (XOR fold) ───────────────────────────────
pub uninterp spec fn single_number_spec(a: Seq<i64>) -> i64;

#[verifier::external_body]
pub fn single_number(a: &[i64]) -> (r: i64)
    requires a@.len() <= 100_000,
    ensures r == single_number_spec(a@),
{
    let mut x: i64 = 0;
    let n = a.len();
    let mut i: usize = 0;
    while i < n { x = x ^ a[i]; i = i + 1; }
    x
}

// ── Missing Number ─────────────────────────────────────────
pub uninterp spec fn missing_number_spec(a: Seq<i64>) -> i64;

#[verifier::external_body]
pub fn missing_number(a: &[i64]) -> (r: i64)
    requires a@.len() <= 100_000,
    ensures r == missing_number_spec(a@),
{
    let n = a.len() as i64;
    let expected: i64 = n * (n + 1) / 2;
    let mut sum: i64 = 0;
    let mut i: usize = 0;
    while i < a.len() { sum = sum + a[i]; i = i + 1; }
    expected - sum
}

// ── Counting Bits ──────────────────────────────────────────
pub uninterp spec fn counting_bits_spec(n: u64) -> Seq<u64>;

#[verifier::external_body]
pub fn counting_bits(n: u64) -> (r: Vec<u64>)
    requires n <= 100_000,
    ensures r@ == counting_bits_spec(n),
{
    let mut out: Vec<u64> = Vec::new();
    out.push(0);
    let mut i: u64 = 1;
    while i <= n { out.push(out[(i / 2) as usize] + (i & 1)); i = i + 1; }
    out
}

// ── Reverse Bits (32-bit) ──────────────────────────────────
pub uninterp spec fn reverse_bits_spec(n: u32) -> u32;

#[verifier::external_body]
pub fn reverse_bits(n: u32) -> (r: u32)
    ensures r == reverse_bits_spec(n),
{
    let mut x = n;
    let mut out: u32 = 0;
    let mut i: u32 = 0;
    while i < 32 {
        out = (out << 1) | (x & 1);
        x = x >> 1;
        i = i + 1;
    }
    out
}

}
