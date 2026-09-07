//! Phase 6 — Arrays & Hashing, Two Pointers, Sliding Window.
//!
//! Composition shapes:
//!
//! - **Hashing**: `ResourceRegistry` as presence set / counter /
//!   index map; aggregations via `Reduction`; top-K via
//!   `CompetitiveSelection::ranked`.
//! - **Two Pointers**: plain converging cursors, needing no
//!   primitive; any running aggregate uses `Reduction`.
//! - **Sliding Window**: `ResourceRegistry` for window contents;
//!   `Reduction` for running aggregates; Sliding Window Maximum uses the
//!   monotonic-deque shape: `ResourceRegistry` plus `ActuationPass`
//!   bidirectional evict.
//!
//! Structural orderings: all Linear except Product of Array Except Self
//! (Tree — two independent scans) and Group Anagrams (Tree — parallel
//! canonicalization steps join at the registry).
//!
//! Every composition draws exclusively from `crate::primitives` and
//! `crate::candidates`. No `std::collections::HashMap` or
//! `std::collections::BinaryHeap` used to do a primitive's job.

use super::{entry, gen};
use crate::config::CorpusEntry;
use crate::equivalence::Equiv;
use crate::primitives::{ActuationPass, CompetitiveSelection, Reduction, ResourceRegistry};
use crate::value::Value;

// =====================================================================
// Contains Duplicate
// ResourceRegistry (presence set) — Bool
// =====================================================================
fn contains_duplicate(input: Value) -> Value {
    let nums = input.as_int_vec();
    let mut seen: ResourceRegistry<i64, ()> = ResourceRegistry::new();
    for x in nums {
        if seen.contains(&x) {
            return Value::Bool(true);
        }
        seen.insert(x, ());
    }
    Value::Bool(false)
}

// =====================================================================
// Two Sum
// ResourceRegistry (complement → index map) — Value::ints sorted asc, Exact
// Input: [ints, Int target]
// =====================================================================
fn two_sum(input: Value) -> Value {
    let parts = input.as_list();
    let nums = parts[0].as_int_vec();
    let target = parts[1].as_int();
    // ResourceRegistry maps value → first index where it appeared.
    let mut comp_map: ResourceRegistry<i64, usize> = ResourceRegistry::new();
    for (i, &x) in nums.iter().enumerate() {
        let complement = target - x;
        if let Some(&j) = comp_map.lookup(&complement) {
            // return sorted ascending
            let mut pair = [j as i64, i as i64];
            pair.sort_unstable();
            return Value::ints(&pair);
        }
        // only insert if not already present (preserve first occurrence)
        if !comp_map.contains(&x) {
            comp_map.insert(x, i);
        }
    }
    // guaranteed to have a solution by problem definition
    Value::ints(&[])
}

// =====================================================================
// Group Anagrams
// ResourceRegistry (canonical key → list of original indices) — SetOfIntLists
// Input: List[Str] — output: list-of-groups of indices
// =====================================================================
fn group_anagrams(input: Value) -> Value {
    let strs = input.as_list();
    // ResourceRegistry: sorted-string key → bucket of indices (as i64)
    let mut buckets: ResourceRegistry<String, Vec<i64>> = ResourceRegistry::new();
    for (i, s) in strs.iter().enumerate() {
        let raw = s.as_str();
        let mut chars: Vec<char> = raw.chars().collect();
        chars.sort_unstable();
        let key: String = chars.into_iter().collect();
        let bucket = buckets.entry_or(key, Vec::new());
        bucket.push(i as i64);
    }
    // collect groups (order of groups is non-deterministic — SetOfIntLists equivalence)
    let groups: Vec<Value> = buckets.values().map(|g| Value::ints(g)).collect();
    Value::List(groups)
}

// =====================================================================
// Top K Frequent Elements
// Reduction(count) + ResourceRegistry + CompetitiveSelection::ranked — MultisetInt
// Input: [ints, Int k]
// =====================================================================
fn top_k_frequent(input: Value) -> Value {
    let parts = input.as_list();
    let nums = parts[0].as_int_vec();
    let k = parts[1].as_int().max(0) as usize;
    // Phase 1: count frequencies via ResourceRegistry + Reduction (sum keyed by element)
    let mut freq: ResourceRegistry<i64, i64> = ResourceRegistry::new();
    for x in &nums {
        let cur = *freq.lookup(x).unwrap_or(&0);
        freq.insert(*x, Reduction::reduce(vec![cur, 1], 0, |a, b| a + b));
    }
    // Collect (element, count) pairs.
    let pairs: Vec<(i64, i64)> = freq
        .keys()
        .map(|&k| (k, *freq.lookup(&k).unwrap()))
        .collect();
    // Phase 2: CompetitiveSelection::ranked — top K by score.
    // Score encodes deterministic tie-breaking: count * SCALE - element_value
    // so higher count wins and lower element value wins on ties — matches the
    // Python oracle's sorted(-count, value) ordering.
    const SCALE: i64 = 1_000_000_000;
    let top = CompetitiveSelection::ranked(&pairs, k, |&(v, c)| c * SCALE - v);
    Value::ints(&top.iter().map(|&(v, _)| v).collect::<Vec<_>>())
}

// =====================================================================
// Product of Array Except Self
// Two Reduction scans (left prefix product, right prefix product) — Value::ints, Exact
// =====================================================================
fn product_except_self(input: Value) -> Value {
    let a = input.as_int_vec();
    let n = a.len();
    if n == 0 {
        return Value::ints(&[]);
    }
    // Left scan: left[i] = product of a[0..i] (exclusive)
    let mut left = vec![1i64; n];
    let mut running = 1i64;
    for i in 0..n {
        left[i] = running;
        running = Reduction::reduce(vec![running, a[i]], 1, |acc, x| acc * x);
    }
    // Right scan: right[i] = product of a[i+1..n] (exclusive)
    let mut right = vec![1i64; n];
    running = 1i64;
    for i in (0..n).rev() {
        right[i] = running;
        running = Reduction::reduce(vec![running, a[i]], 1, |acc, x| acc * x);
    }
    // Pointwise combine
    let out: Vec<i64> = (0..n)
        .map(|i| Reduction::reduce(vec![left[i], right[i]], 1, |acc, x| acc * x))
        .collect();
    Value::ints(&out)
}

// =====================================================================
// Longest Consecutive Sequence
// ResourceRegistry (presence set) + Reduction (running max) — Int, Exact
// =====================================================================
fn longest_consecutive(input: Value) -> Value {
    let a = input.as_int_vec();
    // Build presence set
    let mut present: ResourceRegistry<i64, ()> = ResourceRegistry::new();
    for &x in &a {
        present.insert(x, ());
    }
    let mut best = 0i64;
    for &x in &a {
        // Only start a chain from the sequence start (no predecessor)
        if !present.contains(&(x - 1)) {
            let mut cur = x;
            let mut len = 0i64;
            while present.contains(&cur) {
                cur += 1;
                len += 1;
            }
            best = Reduction::reduce(vec![best, len], 0, |a, b| a.max(b));
        }
    }
    Value::Int(best)
}

// =====================================================================
// Valid Palindrome
// Plain converging cursors, no primitive — Bool
// =====================================================================
fn valid_palindrome(input: Value) -> Value {
    let s: Vec<char> = input.as_str().chars().collect();
    let mut lo = 0usize;
    let mut hi = s.len().saturating_sub(1);
    while lo < hi {
        while lo < hi && !s[lo].is_alphanumeric() {
            lo += 1;
        }
        while lo < hi && !s[hi].is_alphanumeric() {
            hi -= 1;
        }
        if lo < hi {
            if s[lo].to_ascii_lowercase() != s[hi].to_ascii_lowercase() {
                return Value::Bool(false);
            }
            lo += 1;
            hi -= 1;
        }
    }
    Value::Bool(true)
}

// =====================================================================
// Two Sum II (sorted input)
// Plain converging cursors — Value::ints sorted asc, Exact
// Input: [ints, Int target]
// =====================================================================
fn two_sum_ii(input: Value) -> Value {
    let parts = input.as_list();
    let nums = parts[0].as_int_vec();
    let target = parts[1].as_int();
    let mut lo = 0usize;
    let mut hi = nums.len().saturating_sub(1);
    while lo < hi {
        let s = nums[lo] + nums[hi];
        if s == target {
            let mut pair = [lo as i64, hi as i64];
            pair.sort_unstable();
            return Value::ints(&pair);
        } else if s < target {
            lo += 1;
        } else {
            hi -= 1;
        }
    }
    Value::ints(&[])
}

// =====================================================================
// Three Sum
// SortThenSweep: (sort) → converging cursors + ResourceRegistry (triplet dedup) — SetOfIntLists
// Input: List[Int] — output: list of sorted triplets
// =====================================================================
fn three_sum(input: Value) -> Value {
    let mut nums = input.as_int_vec();
    nums.sort_unstable(); // sort is a black-box pre-step, not a catalog primitive
    let n = nums.len();
    // ResourceRegistry to track emitted triplets and avoid duplicates
    let mut seen: ResourceRegistry<(i64, i64, i64), ()> = ResourceRegistry::new();
    let mut result: Vec<Value> = Vec::new();
    for i in 0..n {
        if i > 0 && nums[i] == nums[i - 1] {
            continue;
        }
        let mut lo = i + 1;
        let mut hi = n.saturating_sub(1);
        while lo < hi {
            let s = nums[i] + nums[lo] + nums[hi];
            if s == 0 {
                let key = (nums[i], nums[lo], nums[hi]);
                if !seen.contains(&key) {
                    seen.insert(key, ());
                    result.push(Value::ints(&[nums[i], nums[lo], nums[hi]]));
                }
                lo += 1;
                hi -= 1;
            } else if s < 0 {
                lo += 1;
            } else {
                hi -= 1;
            }
        }
    }
    Value::List(result)
}

// =====================================================================
// Container With Most Water
// Converging cursors + Reduction (running max) — Int, Exact
// =====================================================================
fn container_with_most_water(input: Value) -> Value {
    let h = input.as_int_vec();
    let n = h.len();
    if n < 2 {
        return Value::Int(0);
    }
    let mut lo = 0usize;
    let mut hi = n - 1;
    let mut best = 0i64;
    while lo < hi {
        let area = (hi - lo) as i64 * h[lo].min(h[hi]);
        best = Reduction::reduce(vec![best, area], 0, |a, b| a.max(b));
        if h[lo] < h[hi] {
            lo += 1;
        } else {
            hi -= 1;
        }
    }
    Value::Int(best)
}

// =====================================================================
// Trapping Rain Water
// Two converging cursors + two Reductions (left-max, right-max) — Int, Exact
// =====================================================================
fn trapping_rain_water(input: Value) -> Value {
    let h = input.as_int_vec();
    let n = h.len();
    if n < 2 {
        return Value::Int(0);
    }
    let mut lo = 0usize;
    let mut hi = n - 1;
    let mut left_max = 0i64;
    let mut right_max = 0i64;
    let mut total = 0i64;
    while lo < hi {
        if h[lo] <= h[hi] {
            left_max = Reduction::reduce(vec![left_max, h[lo]], 0, |a, b| a.max(b));
            total += left_max - h[lo];
            lo += 1;
        } else {
            right_max = Reduction::reduce(vec![right_max, h[hi]], 0, |a, b| a.max(b));
            total += right_max - h[hi];
            hi -= 1;
        }
    }
    Value::Int(total)
}

// =====================================================================
// Best Time to Buy and Sell Stock
// Two Reductions interleaved (running min, running max profit) — Int, Exact
// =====================================================================
fn buy_sell_stock(input: Value) -> Value {
    let prices = input.as_int_vec();
    let mut min_price = i64::MAX;
    let mut best_profit = 0i64;
    for &p in &prices {
        min_price = Reduction::reduce(vec![min_price, p], i64::MAX, |a, b| a.min(b));
        let profit = p - min_price;
        best_profit = Reduction::reduce(vec![best_profit, profit], 0, |a, b| a.max(b));
    }
    Value::Int(best_profit)
}

// =====================================================================
// Longest Substring Without Repeating Characters
// ResourceRegistry (char → last-seen index) + Reduction (running max) — Int, Exact
// =====================================================================
fn longest_no_repeat(input: Value) -> Value {
    let s: Vec<char> = input.as_str().chars().collect();
    let mut last_pos: ResourceRegistry<char, usize> = ResourceRegistry::new();
    let mut lo = 0usize;
    let mut best = 0i64;
    for (hi, &c) in s.iter().enumerate() {
        if let Some(&prev) = last_pos.lookup(&c) {
            if prev >= lo {
                lo = prev + 1;
            }
        }
        last_pos.insert(c, hi);
        let len = (hi - lo + 1) as i64;
        best = Reduction::reduce(vec![best, len], 0, |a, b| a.max(b));
    }
    Value::Int(best)
}

// =====================================================================
// Longest Repeating Character Replacement
// ResourceRegistry (char counts) + Reduction (max count, max window) — Int, Exact
// Input: [Str s, Int k]
// =====================================================================
fn longest_repeating_char_replacement(input: Value) -> Value {
    let parts = input.as_list();
    let s: Vec<char> = parts[0].as_str().chars().collect();
    let k = parts[1].as_int().max(0) as usize;
    let n = s.len();
    let mut counts: ResourceRegistry<char, i64> = ResourceRegistry::new();
    let mut lo = 0usize;
    let mut max_count = 0i64;
    let mut best = 0i64;
    for hi in 0..n {
        let c = s[hi];
        let new_cnt = counts.lookup(&c).copied().unwrap_or(0) + 1;
        counts.insert(c, new_cnt);
        // Reduction: running max count of any char in window
        max_count = Reduction::reduce(vec![max_count, new_cnt], 0, |a, b| a.max(b));
        // shrink window if invalid
        while (hi - lo + 1) as i64 - max_count > k as i64 {
            let lc = s[lo];
            let lv = counts.lookup(&lc).copied().unwrap_or(0);
            counts.insert(lc, lv - 1);
            lo += 1;
        }
        let win = (hi - lo + 1) as i64;
        best = Reduction::reduce(vec![best, win], 0, |a, b| a.max(b));
    }
    Value::Int(best)
}

// =====================================================================
// Minimum Window Substring
// Two ResourceRegistrys + two Reductions — Str (Value::Str), Exact
// Input: [Str s, Str t]
// =====================================================================
fn min_window_substring(input: Value) -> Value {
    let parts = input.as_list();
    let s: Vec<char> = parts[0].as_str().chars().collect();
    let t: Vec<char> = parts[1].as_str().chars().collect();
    if t.is_empty() {
        return Value::Str(String::new());
    }
    // required counts from t
    let mut required: ResourceRegistry<char, i64> = ResourceRegistry::new();
    for &c in &t {
        let v = required.lookup(&c).copied().unwrap_or(0);
        required.insert(c, v + 1);
    }
    let need = required.len(); // number of distinct chars to satisfy
                               // window counts
    let mut window: ResourceRegistry<char, i64> = ResourceRegistry::new();
    // Reduction: count of distinct required chars whose window count >= required
    let mut satisfied = 0usize;
    let mut lo = 0usize;
    let mut best_len = usize::MAX;
    let mut best_start = 0usize;
    for hi in 0..s.len() {
        let c = s[hi];
        let new_cnt = window.lookup(&c).copied().unwrap_or(0) + 1;
        window.insert(c, new_cnt);
        if let Some(&req) = required.lookup(&c) {
            if new_cnt == req {
                satisfied += 1;
            }
        }
        while satisfied == need {
            let win = hi - lo + 1;
            if win < best_len {
                best_len = win;
                best_start = lo;
            }
            let lc = s[lo];
            let lv = window.lookup(&lc).copied().unwrap_or(0);
            window.insert(lc, lv - 1);
            if let Some(&req) = required.lookup(&lc) {
                if lv - 1 < req {
                    satisfied -= 1;
                }
            }
            lo += 1;
        }
    }
    if best_len == usize::MAX {
        Value::Str(String::new())
    } else {
        Value::Str(s[best_start..best_start + best_len].iter().collect())
    }
}

// =====================================================================
// Sliding Window Maximum
// monotonic deque of indices (substrate buffer) + ActuationPass (bidirectional
// evict) — Value::ints, Exact
// Input: [ints, Int k]
// =====================================================================
fn sliding_window_maximum(input: Value) -> Value {
    let parts = input.as_list();
    let a = parts[0].as_int_vec();
    let k = parts[1].as_int().max(1) as usize;
    let n = a.len();
    if n == 0 || k == 0 {
        return Value::ints(&[]);
    }
    // The deque is a substrate buffer (a VecDeque<usize> of indices into a — a
    // positional buffer, not a ResourceRegistry), maintained under the
    // monotonicity invariant a[deque[front]] >= a[deque[back]] (decreasing
    // front→back). ActuationPass performs the evictions on both ends.
    let mut deque: std::collections::VecDeque<usize> = std::collections::VecDeque::new();
    let mut result: Vec<i64> = Vec::new();
    for i in 0..n {
        // Count trailing elements with values <= a[i] (an immutable borrow);
        // they can never be the maximum while a[i] is in the window.
        let mut back_evict = 0usize;
        while back_evict < deque.len() && a[deque[deque.len() - 1 - back_evict]] <= a[i] {
            back_evict += 1;
        }
        // ActuationPass: evict them from the back.
        ActuationPass::apply_each(0..back_evict, |_| {
            deque.pop_back();
        });
        deque.push_back(i);
        // Count leading elements that have exited the window, then evict them.
        let mut front_evict = 0usize;
        while front_evict < deque.len() && deque[front_evict] + k <= i {
            front_evict += 1;
        }
        // ActuationPass: evict them from the front.
        ActuationPass::apply_each(0..front_evict, |_| {
            deque.pop_front();
        });
        if i + 1 >= k {
            result.push(a[*deque.front().unwrap()]);
        }
    }
    Value::ints(&result)
}

// =============================================================================
// Input generators
// =============================================================================

fn g_contains_dup() -> Vec<Value> {
    let mut v = vec![
        Value::ints(&[]),
        Value::ints(&[1]),
        Value::ints(&[1, 2, 3]),
        Value::ints(&[1, 2, 3, 1]),
        Value::ints(&[0, 0]),
        Value::ints(&[-1, -2, -1]),
    ];
    v.extend(gen::rand_int_lists(60, 1000, 12, -10, 10));
    v
}

fn g_two_sum() -> Vec<Value> {
    let curated = vec![
        Value::List(vec![Value::ints(&[2, 7, 11, 15]), Value::Int(9)]),
        Value::List(vec![Value::ints(&[3, 2, 4]), Value::Int(6)]),
        Value::List(vec![Value::ints(&[3, 3]), Value::Int(6)]),
        Value::List(vec![Value::ints(&[0, -1, 2, -3, 1]), Value::Int(-2)]),
    ];
    let mut v = curated;
    // Property: construct pairs with known answers
    let mut s = crate::primitives::Sampler::new(61);
    for _ in 0..1000 {
        let n = 2 + s.pick_index(8);
        let mut nums: Vec<i64> = (0..n).map(|_| s.pick_index(20) as i64 - 10).collect();
        // ensure a valid pair exists at positions 0 and 1
        nums[0] = s.pick_index(10) as i64 - 5;
        nums[1] = s.pick_index(10) as i64 - 5;
        let target = nums[0] + nums[1];
        // shuffle to avoid always returning [0,1]
        let swap_pos = 1 + s.pick_index(n - 1);
        nums.swap(0, swap_pos);
        v.push(Value::List(vec![Value::ints(&nums), Value::Int(target)]));
    }
    v
}

fn g_group_anagrams() -> Vec<Value> {
    let strs = |ss: &[&str]| Value::List(ss.iter().map(|&s| Value::Str(s.to_string())).collect());
    let mut v = vec![
        strs(&["eat", "tea", "tan", "ate", "nat", "bat"]),
        strs(&[""]),
        strs(&["a"]),
        strs(&["ab", "ba", "abc", "bca", "cab", "xyz"]),
    ];
    // property: random strings, anagrams by construction
    let mut s = crate::primitives::Sampler::new(62);
    for _ in 0..500 {
        let n = 1 + s.pick_index(5);
        let mut group: Vec<String> = Vec::new();
        // build one base string and shuffle copies
        let len = 2 + s.pick_index(4);
        let base: Vec<u8> = (0..len).map(|_| b'a' + s.pick_index(4) as u8).collect();
        for _ in 0..n {
            let mut perm = base.clone();
            // simple pseudo-shuffle
            for i in (1..perm.len()).rev() {
                let j = s.pick_index(i + 1);
                perm.swap(i, j);
            }
            group.push(String::from_utf8(perm).unwrap());
        }
        // add some unrelated strings
        let extra: usize = s.pick_index(3);
        for _ in 0..extra {
            let elen = 1 + s.pick_index(4);
            let es: String = (0..elen)
                .map(|_| (b'e' + s.pick_index(3) as u8) as char)
                .collect();
            group.push(es);
        }
        let all: Vec<Value> = group.into_iter().map(|w| Value::Str(w)).collect();
        v.push(Value::List(all));
    }
    v
}

fn g_top_k() -> Vec<Value> {
    let curated = vec![
        Value::List(vec![Value::ints(&[1, 1, 1, 2, 2, 3]), Value::Int(2)]),
        Value::List(vec![Value::ints(&[1]), Value::Int(1)]),
        Value::List(vec![Value::ints(&[1, 2]), Value::Int(2)]),
        Value::List(vec![Value::ints(&[3, 0, 1, 0]), Value::Int(1)]),
    ];
    let mut v = curated;
    let mut s = crate::primitives::Sampler::new(63);
    for _ in 0..1000 {
        let n = 2 + s.pick_index(8);
        let nums: Vec<i64> = (0..n).map(|_| s.pick_index(5) as i64).collect();
        let k = (1 + s.pick_index(3)).min(n) as i64;
        v.push(Value::List(vec![Value::ints(&nums), Value::Int(k)]));
    }
    v
}

fn g_product_except_self() -> Vec<Value> {
    let mut v = vec![
        Value::ints(&[1, 2, 3, 4]),
        Value::ints(&[-1, 1, 0, -3, 3]),
        Value::ints(&[0, 0]),
        Value::ints(&[1]),
        Value::ints(&[]),
    ];
    v.extend(gen::rand_int_lists(64, 1000, 8, -5, 5));
    v
}

fn g_longest_consecutive() -> Vec<Value> {
    let mut v = vec![
        Value::ints(&[100, 4, 200, 1, 3, 2]),
        Value::ints(&[0, 3, 7, 2, 5, 8, 4, 6, 0, 1]),
        Value::ints(&[]),
        Value::ints(&[1]),
        Value::ints(&[1, 1, 1]),
    ];
    v.extend(gen::rand_int_lists(65, 1000, 12, -10, 10));
    v
}

fn g_valid_palindrome() -> Vec<Value> {
    let strs = |s: &str| Value::Str(s.to_string());
    let mut v = vec![
        strs("A man, a plan, a canal: Panama"),
        strs("race a car"),
        strs(" "),
        strs(""),
        strs("ab_a"),
        strs("0P"),
    ];
    v.extend(gen::rand_strings(66, 1000, 12, 4));
    v
}

fn g_two_sum_ii() -> Vec<Value> {
    let curated = vec![
        Value::List(vec![Value::ints(&[2, 7, 11, 15]), Value::Int(9)]),
        Value::List(vec![Value::ints(&[2, 3, 4]), Value::Int(6)]),
        Value::List(vec![Value::ints(&[-1, 0]), Value::Int(-1)]),
    ];
    let mut v = curated;
    let mut s = crate::primitives::Sampler::new(67);
    for _ in 0..1000 {
        let n = 2 + s.pick_index(7);
        let mut nums: Vec<i64> = (0..n).map(|_| s.pick_index(20) as i64 - 10).collect();
        nums.sort_unstable();
        // pick two distinct positions for the target pair
        let i = s.pick_index(n - 1);
        let j = i + 1 + s.pick_index(n - i - 1);
        let target = nums[i] + nums[j];
        v.push(Value::List(vec![Value::ints(&nums), Value::Int(target)]));
    }
    v
}

fn g_three_sum() -> Vec<Value> {
    let mut v = vec![
        Value::ints(&[-1, 0, 1, 2, -1, -4]),
        Value::ints(&[0, 1, 1]),
        Value::ints(&[0, 0, 0]),
        Value::ints(&[]),
        Value::ints(&[-2, 0, 1, 1, 2]),
    ];
    v.extend(gen::rand_int_lists(68, 1000, 10, -5, 5));
    v
}

fn g_container_water() -> Vec<Value> {
    let mut v = vec![
        Value::ints(&[1, 8, 6, 2, 5, 4, 8, 3, 7]),
        Value::ints(&[1, 1]),
        Value::ints(&[4, 3, 2, 1, 4]),
        Value::ints(&[1, 2, 1]),
    ];
    v.extend(gen::rand_int_lists(69, 1000, 10, 0, 10));
    v
}

fn g_trap_rain() -> Vec<Value> {
    let mut v = vec![
        Value::ints(&[0, 1, 0, 2, 1, 0, 1, 3, 2, 1, 2, 1]),
        Value::ints(&[4, 2, 0, 3, 2, 5]),
        Value::ints(&[]),
        Value::ints(&[3, 0, 3]),
    ];
    v.extend(gen::rand_int_lists(70, 1000, 10, 0, 6));
    v
}

fn g_buy_sell() -> Vec<Value> {
    let mut v = vec![
        Value::ints(&[7, 1, 5, 3, 6, 4]),
        Value::ints(&[7, 6, 4, 3, 1]),
        Value::ints(&[1]),
        Value::ints(&[]),
    ];
    v.extend(gen::rand_int_lists(71, 1000, 10, 0, 20));
    v
}

fn g_longest_no_repeat() -> Vec<Value> {
    let mut v = vec![
        Value::Str("abcabcbb".into()),
        Value::Str("bbbbb".into()),
        Value::Str("pwwkew".into()),
        Value::Str("".into()),
        Value::Str(" ".into()),
        Value::Str("dvdf".into()),
    ];
    v.extend(gen::rand_strings(72, 1000, 12, 6));
    v
}

fn g_char_replacement() -> Vec<Value> {
    let curated = vec![
        Value::List(vec![Value::Str("ABAB".into()), Value::Int(2)]),
        Value::List(vec![Value::Str("AABABBA".into()), Value::Int(1)]),
        Value::List(vec![Value::Str("".into()), Value::Int(0)]),
        Value::List(vec![Value::Str("A".into()), Value::Int(0)]),
    ];
    let mut v = curated;
    let strings = gen::rand_strings(73, 1000, 10, 4);
    let mut s = crate::primitives::Sampler::new(730);
    for st in strings {
        let k = s.pick_index(5) as i64;
        v.push(Value::List(vec![st, Value::Int(k)]));
    }
    v
}

fn g_min_window() -> Vec<Value> {
    let curated = vec![
        Value::List(vec![
            Value::Str("ADOBECODEBANC".into()),
            Value::Str("ABC".into()),
        ]),
        Value::List(vec![Value::Str("a".into()), Value::Str("a".into())]),
        Value::List(vec![Value::Str("a".into()), Value::Str("aa".into())]),
        Value::List(vec![Value::Str("".into()), Value::Str("A".into())]),
        Value::List(vec![Value::Str("ABC".into()), Value::Str("".into())]),
    ];
    let mut v = curated;
    let s_strs = gen::rand_strings(74, 500, 12, 4);
    let t_strs = gen::rand_strings(75, 500, 4, 4);
    for (s, t) in s_strs.into_iter().zip(t_strs) {
        v.push(Value::List(vec![s, t]));
    }
    v
}

fn g_sliding_max() -> Vec<Value> {
    let curated = vec![
        Value::List(vec![
            Value::ints(&[1, 3, -1, -3, 5, 3, 6, 7]),
            Value::Int(3),
        ]),
        Value::List(vec![Value::ints(&[1]), Value::Int(1)]),
        Value::List(vec![Value::ints(&[1, -1]), Value::Int(1)]),
        Value::List(vec![Value::ints(&[9, 11]), Value::Int(2)]),
        Value::List(vec![Value::ints(&[4, -2]), Value::Int(2)]),
        Value::List(vec![Value::ints(&[]), Value::Int(3)]),
    ];
    let mut v = curated;
    let mut s = crate::primitives::Sampler::new(76);
    for _ in 0..1000 {
        let n = 1 + s.pick_index(10);
        let nums: Vec<i64> = (0..n).map(|_| s.pick_index(20) as i64 - 10).collect();
        let k = (1 + s.pick_index(n)) as i64;
        v.push(Value::List(vec![Value::ints(&nums), Value::Int(k)]));
    }
    v
}

// =============================================================================
// Registry
// =============================================================================

pub fn add(r: &mut Vec<CorpusEntry>) {
    let reg_p = "ResourceRegistry(presence)";
    let reg_ci = "ResourceRegistry(complement-index)";
    let reg_bk = "ResourceRegistry(canonical-bucket)";
    let reg_rd_cs = "ResourceRegistry(counter) + Reduction(sum) + CompetitiveSelection(ranked)";
    let red2 = "Reduction(prefix-product) x2";
    let reg_r = "ResourceRegistry(presence) + Reduction(max)";
    let red_interleaved = "Reduction(running-min) + Reduction(running-max)";
    let reg_wn = "ResourceRegistry(window-char) + Reduction(window-max)";
    let reg_cc = "ResourceRegistry(char-counts) + Reduction(max-count) + Reduction(window-max)";
    let reg2_r2 = "ResourceRegistry(window-counts) + ResourceRegistry(required) + Reduction(meet-count) + Reduction(min-window)";
    let reg_ap = "monotonic deque (substrate buffer) + ActuationPass(bidirectional-evict)";

    entry(
        r,
        "Contains Duplicate",
        "Arrays & Hashing",
        6,
        "Linear",
        reg_p,
        contains_duplicate,
        "contains_duplicate",
        Equiv::BoolEq,
        g_contains_dup,
    );
    entry(
        r,
        "Two Sum",
        "Arrays & Hashing",
        6,
        "Linear",
        reg_ci,
        two_sum,
        "two_sum",
        Equiv::Exact,
        g_two_sum,
    );
    entry(
        r,
        "Group Anagrams",
        "Arrays & Hashing",
        6,
        "Tree",
        reg_bk,
        group_anagrams,
        "group_anagrams",
        Equiv::SetOfIntLists,
        g_group_anagrams,
    );
    entry(
        r,
        "Top K Frequent",
        "Arrays & Hashing",
        6,
        "Tree",
        reg_rd_cs,
        top_k_frequent,
        "top_k_frequent",
        Equiv::MultisetInt,
        g_top_k,
    );
    entry(
        r,
        "Product Except Self",
        "Arrays & Hashing",
        6,
        "Tree",
        red2,
        product_except_self,
        "product_except_self",
        Equiv::Exact,
        g_product_except_self,
    );
    entry(
        r,
        "Longest Consecutive",
        "Arrays & Hashing",
        6,
        "Tree",
        reg_r,
        longest_consecutive,
        "longest_consecutive",
        Equiv::Exact,
        g_longest_consecutive,
    );

    entry(
        r,
        "Valid Palindrome",
        "Two Pointers",
        6,
        "Linear",
        "cursors (no primitive)",
        valid_palindrome,
        "valid_palindrome",
        Equiv::BoolEq,
        g_valid_palindrome,
    );
    entry(
        r,
        "Two Sum II",
        "Two Pointers",
        6,
        "Linear",
        "cursors (no primitive)",
        two_sum_ii,
        "two_sum_ii",
        Equiv::Exact,
        g_two_sum_ii,
    );
    entry(
        r,
        "Three Sum",
        "Two Pointers",
        6,
        "Tree",
        "SortThenSweep: (sort) + cursors + ResourceRegistry(triplet dedup)",
        three_sum,
        "three_sum",
        Equiv::SetOfIntLists,
        g_three_sum,
    );
    entry(
        r,
        "Container With Most Water",
        "Two Pointers",
        6,
        "Linear",
        "cursors + Reduction(running-max)",
        container_with_most_water,
        "container_with_most_water",
        Equiv::Exact,
        g_container_water,
    );
    entry(
        r,
        "Trapping Rain Water",
        "Two Pointers",
        6,
        "Linear",
        "cursors + Reduction(left-max) + Reduction(right-max)",
        trapping_rain_water,
        "trapping_rain_water",
        Equiv::Exact,
        g_trap_rain,
    );

    entry(
        r,
        "Buy Sell Stock",
        "Sliding Window",
        6,
        "Linear",
        red_interleaved,
        buy_sell_stock,
        "buy_sell_stock",
        Equiv::Exact,
        g_buy_sell,
    );
    entry(
        r,
        "Longest No Repeat",
        "Sliding Window",
        6,
        "Linear",
        reg_wn,
        longest_no_repeat,
        "longest_no_repeat",
        Equiv::Exact,
        g_longest_no_repeat,
    );
    entry(
        r,
        "Char Replacement",
        "Sliding Window",
        6,
        "Linear",
        reg_cc,
        longest_repeating_char_replacement,
        "char_replacement",
        Equiv::Exact,
        g_char_replacement,
    );
    entry(
        r,
        "Min Window Substring",
        "Sliding Window",
        6,
        "Linear",
        reg2_r2,
        min_window_substring,
        "min_window_substring",
        Equiv::Exact,
        g_min_window,
    );
    entry(
        r,
        "Sliding Window Max",
        "Sliding Window",
        6,
        "Linear",
        reg_ap,
        sliding_window_maximum,
        "sliding_window_max",
        Equiv::Exact,
        g_sliding_max,
    );
}
