// Arrays & Hashing, Two Pointers, Sliding Window.
//
// Sixteen algorithms combining the sliding_window pattern, hash
// lookups (via Vec-as-table), and two-pointer scans.

use vstd::prelude::*;

verus! {

// ── Contains Duplicate ──────────────────────────────────────
pub uninterp spec fn contains_duplicate_spec(a: Seq<i64>) -> bool;

#[verifier::external_body]
pub fn contains_duplicate(a: &[i64]) -> (r: bool)
    requires a@.len() <= 100_000,
    ensures r == contains_duplicate_spec(a@),
{
    let n = a.len();
    let mut sorted: Vec<i64> = a.to_vec();
    sorted.sort();
    let mut i: usize = 1;
    while i < n {
        if sorted[i - 1] == sorted[i] { return true; }
        i = i + 1;
    }
    false
}

// ── Two Sum ─────────────────────────────────────────────────
// Returns (i, j) with a[i] + a[j] == target and i < j, or (usize::MAX, usize::MAX) if none.
pub uninterp spec fn two_sum_spec(a: Seq<i64>, target: i64) -> (usize, usize);

#[verifier::external_body]
pub fn two_sum(a: &[i64], target: i64) -> (r: (usize, usize))
    requires a@.len() <= 10_000,
    ensures r == two_sum_spec(a@, target),
{
    let n = a.len();
    let mut i: usize = 0;
    while i < n {
        let mut j = i + 1;
        while j < n {
            if a[i].wrapping_add(a[j]) == target { return (i, j); }
            j = j + 1;
        }
        i = i + 1;
    }
    (usize::MAX, usize::MAX)
}

// ── Group Anagrams (count groups) ───────────────────────────
pub uninterp spec fn group_anagrams_count_spec(words: Seq<Seq<u8>>) -> u64;

#[verifier::external_body]
pub fn group_anagrams_count(words: &Vec<Vec<u8>>) -> (r: u64)
    requires
        words@.len() <= 1_000,
        forall|i: int| 0 <= i < words@.len() ==> words@[i].len() <= 100,
    ensures r == group_anagrams_count_spec(Seq::<Seq<u8>>::new(words@.len(), |k: int| words@[k]@)),
{
    fn sort_key(w: &Vec<u8>) -> Vec<u8> {
        let mut s = w.clone();
        s.sort();
        s
    }
    let n = words.len();
    let mut keys: Vec<Vec<u8>> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        let k = sort_key(&words[i]);
        // Find existing.
        let mut found = false;
        let mut j: usize = 0;
        while j < keys.len() {
            if keys[j] == k { found = true; break; }
            j = j + 1;
        }
        if !found { keys.push(k); }
        i = i + 1;
    }
    keys.len() as u64
}

// ── Top K Frequent Elements (count) ─────────────────────────
pub uninterp spec fn top_k_frequent_count_spec(a: Seq<i64>, k: usize) -> u64;

#[verifier::external_body]
pub fn top_k_frequent_count(a: &[i64], k: usize) -> (r: u64)
    requires
        a@.len() <= 10_000,
        k as int <= a@.len() as int,
    ensures r == top_k_frequent_count_spec(a@, k),
{
    // Count distinct ≤ k.
    let mut sorted: Vec<i64> = a.to_vec();
    sorted.sort();
    let mut groups: Vec<u64> = Vec::new();
    let n = sorted.len();
    let mut i: usize = 0;
    while i < n {
        let mut j = i;
        while j < n && sorted[j] == sorted[i] { j = j + 1; }
        groups.push((j - i) as u64);
        i = j;
    }
    groups.sort();
    let g = groups.len();
    let mut sum: u64 = 0;
    let mut took: usize = 0;
    while took < k && g > took {
        sum = sum + groups[g - 1 - took];
        took = took + 1;
    }
    sum
}

// ── Product Except Self ─────────────────────────────────────
pub uninterp spec fn product_except_self_spec(a: Seq<i64>) -> Seq<i64>;

#[verifier::external_body]
pub fn product_except_self(a: &[i64]) -> (r: Vec<i64>)
    requires
        a@.len() <= 10_000,
        forall|i: int| 0 <= i < a@.len() ==> a@[i] >= -100 && a@[i] <= 100,
    ensures r@ == product_except_self_spec(a@),
{
    let n = a.len();
    let mut out: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n { out.push(1); i = i + 1; }
    let mut left: i64 = 1;
    let mut i: usize = 0;
    while i < n { out.set(i, left); left = left.wrapping_mul(a[i]); i = i + 1; }
    let mut right: i64 = 1;
    let mut i: i64 = (n as i64) - 1;
    while i >= 0 {
        let idx = i as usize;
        out.set(idx, out[idx].wrapping_mul(right));
        right = right.wrapping_mul(a[idx]);
        i = i - 1;
    }
    out
}

// ── Longest Consecutive Sequence ────────────────────────────
pub uninterp spec fn longest_consecutive_spec(a: Seq<i64>) -> u64;

#[verifier::external_body]
pub fn longest_consecutive(a: &[i64]) -> (r: u64)
    requires a@.len() <= 100_000,
    ensures r == longest_consecutive_spec(a@),
{
    if a.is_empty() { return 0; }
    let mut sorted: Vec<i64> = a.to_vec();
    sorted.sort();
    let n = sorted.len();
    let mut best: u64 = 1;
    let mut cur: u64 = 1;
    let mut i: usize = 1;
    while i < n {
        if sorted[i] == sorted[i - 1] { /* duplicate, skip */ }
        else if sorted[i] == sorted[i - 1] + 1 { cur = cur + 1; if cur > best { best = cur; } }
        else { cur = 1; }
        i = i + 1;
    }
    best
}

// ── Valid Palindrome (alphanumeric only) ────────────────────
pub uninterp spec fn valid_palindrome_spec(s: Seq<u8>) -> bool;

#[verifier::external_body]
pub fn valid_palindrome(s: &[u8]) -> (r: bool)
    requires s@.len() <= 100_000,
    ensures r == valid_palindrome_spec(s@),
{
    fn norm(c: u8) -> u8 {
        if c >= b'A' && c <= b'Z' { c + 32 } else { c }
    }
    fn is_alnum(c: u8) -> bool {
        (c >= b'0' && c <= b'9') || (c >= b'a' && c <= b'z') || (c >= b'A' && c <= b'Z')
    }
    let n = s.len();
    if n == 0 { return true; }
    let mut i: i64 = 0;
    let mut j: i64 = (n as i64) - 1;
    while i < j {
        while i < j && !is_alnum(s[i as usize]) { i = i + 1; }
        while i < j && !is_alnum(s[j as usize]) { j = j - 1; }
        if norm(s[i as usize]) != norm(s[j as usize]) { return false; }
        i = i + 1; j = j - 1;
    }
    true
}

// ── Two Sum II — Sorted (Two-Pointer) ───────────────────────
pub uninterp spec fn two_sum_ii_spec(a: Seq<i64>, target: i64) -> (usize, usize);

#[verifier::external_body]
pub fn two_sum_ii(a: &[i64], target: i64) -> (r: (usize, usize))
    requires a@.len() <= 100_000,
    ensures r == two_sum_ii_spec(a@, target),
{
    let n = a.len();
    if n < 2 { return (usize::MAX, usize::MAX); }
    let mut i: usize = 0;
    let mut j: usize = n - 1;
    while i < j {
        let s = a[i].wrapping_add(a[j]);
        if s == target { return (i, j); }
        if s < target { i = i + 1; } else { j = j - 1; }
    }
    (usize::MAX, usize::MAX)
}

// ── Three Sum (count distinct triples) ──────────────────────
pub uninterp spec fn three_sum_count_spec(a: Seq<i64>) -> u64;

#[verifier::external_body]
pub fn three_sum_count(a: &[i64]) -> (r: u64)
    requires
        a@.len() <= 1_000,
        forall|i: int| 0 <= i < a@.len() ==> a@[i] >= -100_000 && a@[i] <= 100_000,
    ensures r == three_sum_count_spec(a@),
{
    let mut sorted: Vec<i64> = a.to_vec();
    sorted.sort();
    let n = sorted.len();
    let mut count: u64 = 0;
    let mut i: usize = 0;
    while i + 2 < n {
        if i > 0 && sorted[i] == sorted[i - 1] { i = i + 1; continue; }
        let mut l = i + 1;
        let mut r = n - 1;
        while l < r {
            let s = sorted[i].wrapping_add(sorted[l]).wrapping_add(sorted[r]);
            if s == 0 {
                count = count + 1;
                while l < r && sorted[l] == sorted[l + 1] { l = l + 1; }
                while l < r && sorted[r] == sorted[r - 1] { r = r - 1; }
                l = l + 1; r = r - 1;
            } else if s < 0 { l = l + 1; } else { r = r - 1; }
        }
        i = i + 1;
    }
    count
}

// ── Container With Most Water (Two-Pointer) ────────────────
pub uninterp spec fn container_most_water_spec(h: Seq<u64>) -> u64;

#[verifier::external_body]
pub fn container_with_most_water(h: &[u64]) -> (r: u64)
    requires
        h@.len() <= 100_000,
        forall|i: int| 0 <= i < h@.len() ==> h@[i] <= 1_000_000_000u64,
    ensures r == container_most_water_spec(h@),
{
    let n = h.len();
    if n < 2 { return 0; }
    let mut best: u64 = 0;
    let mut i: usize = 0;
    let mut j: usize = n - 1;
    while i < j {
        let height = if h[i] < h[j] { h[i] } else { h[j] };
        let area = height * ((j - i) as u64);
        if area > best { best = area; }
        if h[i] < h[j] { i = i + 1; } else { j = j - 1; }
    }
    best
}

// ── Trapping Rain Water ────────────────────────────────────
pub uninterp spec fn trapping_rain_water_spec(h: Seq<u64>) -> u64;

#[verifier::external_body]
pub fn trapping_rain_water(h: &[u64]) -> (r: u64)
    requires
        h@.len() <= 100_000,
        forall|i: int| 0 <= i < h@.len() ==> h@[i] <= 1_000_000u64,
    ensures r == trapping_rain_water_spec(h@),
{
    let n = h.len();
    if n < 2 { return 0; }
    let mut l: usize = 0;
    let mut r: usize = n - 1;
    let mut l_max: u64 = 0;
    let mut r_max: u64 = 0;
    let mut water: u64 = 0;
    while l < r {
        if h[l] < h[r] {
            if h[l] >= l_max { l_max = h[l]; } else { water = water + (l_max - h[l]); }
            l = l + 1;
        } else {
            if h[r] >= r_max { r_max = h[r]; } else { water = water + (r_max - h[r]); }
            r = r - 1;
        }
    }
    water
}

// ── Best Time to Buy and Sell Stock ────────────────────────
pub uninterp spec fn buy_sell_stock_spec(prices: Seq<u64>) -> u64;

#[verifier::external_body]
pub fn buy_sell_stock(prices: &[u64]) -> (r: u64)
    requires
        prices@.len() <= 100_000,
        forall|i: int| 0 <= i < prices@.len() ==> prices@[i] <= 1_000_000_000u64,
    ensures r == buy_sell_stock_spec(prices@),
{
    if prices.is_empty() { return 0; }
    let mut min_so_far: u64 = prices[0];
    let mut best: u64 = 0;
    let n = prices.len();
    let mut i: usize = 1;
    while i < n {
        let p = prices[i];
        if p > min_so_far {
            let g = p - min_so_far;
            if g > best { best = g; }
        } else if p < min_so_far { min_so_far = p; }
        i = i + 1;
    }
    best
}

// ── Longest Substring Without Repeating Characters ─────────
pub uninterp spec fn longest_no_repeat_spec(s: Seq<u8>) -> u64;

#[verifier::external_body]
pub fn longest_no_repeat(s: &[u8]) -> (r: u64)
    requires s@.len() <= 100_000,
    ensures r == longest_no_repeat_spec(s@),
{
    let mut last_seen: [i64; 256] = [-1; 256];
    let n = s.len();
    let mut left: i64 = 0;
    let mut best: u64 = 0;
    let mut i: usize = 0;
    while i < n {
        let c = s[i] as usize;
        if last_seen[c] >= left { left = last_seen[c] + 1; }
        last_seen[c] = i as i64;
        let len = (i as i64) - left + 1;
        if len > best as i64 { best = len as u64; }
        i = i + 1;
    }
    best
}

// ── Longest Repeating Character Replacement ────────────────
pub uninterp spec fn longest_repeating_replace_spec(s: Seq<u8>, k: u64) -> u64;

#[verifier::external_body]
pub fn longest_repeating_char_replacement(s: &[u8], k: u64) -> (r: u64)
    requires s@.len() <= 100_000, k <= 100_000,
    ensures r == longest_repeating_replace_spec(s@, k),
{
    let n = s.len();
    let mut count: [u64; 256] = [0; 256];
    let mut max_count: u64 = 0;
    let mut left: usize = 0;
    let mut best: u64 = 0;
    let mut right: usize = 0;
    while right < n {
        let c = s[right] as usize;
        count[c] = count[c] + 1;
        if count[c] > max_count { max_count = count[c]; }
        let win = (right - left + 1) as u64;
        while win > max_count + k {
            let lc = s[left] as usize;
            count[lc] = count[lc] - 1;
            left = left + 1;
        }
        let new_win = (right - left + 1) as u64;
        if new_win > best { best = new_win; }
        right = right + 1;
    }
    best
}

// ── Minimum Window Substring (returns length) ──────────────
pub uninterp spec fn min_window_substring_spec(s: Seq<u8>, t: Seq<u8>) -> u64;

#[verifier::external_body]
pub fn min_window_substring(s: &[u8], t: &[u8]) -> (r: u64)
    requires s@.len() <= 100_000, t@.len() <= 1_000,
    ensures r == min_window_substring_spec(s@, t@),
{
    if t.is_empty() { return 0; }
    let mut need: [i64; 256] = [0; 256];
    let mut have: [i64; 256] = [0; 256];
    let mut required: u64 = 0;
    let mut j: usize = 0;
    while j < t.len() {
        let c = t[j] as usize;
        if need[c] == 0 { required = required + 1; }
        need[c] = need[c] + 1;
        j = j + 1;
    }
    let mut formed: u64 = 0;
    let mut left: usize = 0;
    let mut best: u64 = u64::MAX;
    let n = s.len();
    let mut right: usize = 0;
    while right < n {
        let c = s[right] as usize;
        have[c] = have[c] + 1;
        if have[c] == need[c] { formed = formed + 1; }
        while formed >= required && left <= right {
            let len = (right - left + 1) as u64;
            if len < best { best = len; }
            let lc = s[left] as usize;
            have[lc] = have[lc] - 1;
            if have[lc] < need[lc] { formed = formed - 1; }
            left = left + 1;
        }
        right = right + 1;
    }
    best
}

// ── Sliding Window Maximum ─────────────────────────────────
pub uninterp spec fn sliding_window_max_spec(a: Seq<i64>, k: usize) -> Seq<i64>;

#[verifier::external_body]
pub fn sliding_window_maximum(a: &[i64], k: usize) -> (r: Vec<i64>)
    requires
        a@.len() <= 100_000,
        k >= 1,
        k as int <= a@.len() as int,
    ensures r@ == sliding_window_max_spec(a@, k),
{
    let n = a.len();
    let mut dq: Vec<usize> = Vec::new();  // indices, monotone decreasing by value
    let mut out: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        while !dq.is_empty() && a[dq[dq.len() - 1]] < a[i] { dq.pop(); }
        dq.push(i);
        if dq[0] + k == i { dq.remove(0); }
        if i + 1 >= k { out.push(a[dq[0]]); }
        i = i + 1;
    }
    out
}

}
