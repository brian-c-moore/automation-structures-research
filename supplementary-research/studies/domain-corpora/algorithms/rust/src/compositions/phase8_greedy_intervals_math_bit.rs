//! Phase 8 — Greedy, Intervals, Math & Geometry, Bit Manipulation.
//!
//! Composition shapes by category:
//!
//! **Greedy — Linear Reduction.**
//!   Kadane/Jump/Gas: running-aggregate `Reduction` over a single pass.
//!   Hand of Straights: SortThenSweep — (sort distinct cards) +
//!   `ResourceRegistry` (frequency counts); the sort gives the order.
//!
//! **Intervals — Sort-then-Reduction.**
//!   Merge/Insert: `Reduction` over a sorted interval sequence.
//!   Non-overlapping: `Reduction` (running count) over sort-by-end sweep.
//!   Meeting Rooms II: `PriorityQueue<Reverse<i64>>` (min-heap of end
//!   times) — `CompetitiveSelection::hard` as a data structure.
//!
//! **Math & Geometry — ActuationPass / Bisection+Reduction.**
//!   Rotate Image, Set Matrix Zeroes: `ActuationPass` (two-pass in-place).
//!   Spiral Matrix: `TraversalEngine` bounded-state walk (the four bounds are cursor state).
//!   Pow(x,n): `Bisection` over exponent bits + `Reduction` (product).
//!     INTEGER base / non-negative exponent for exact `Int` output.
//!   Happy Number: Floyd cycle detection, which is structural and uses no
//!     catalog primitive.
//!
//! **Bit Manipulation — Reduction / Memoization / ActuationPass.**
//!   Hamming Weight / Single Number / Missing Number: `Reduction`.
//!   Counting Bits: Memoization = `ResourceRegistry` + `Reduction` (DAG).
//!   Reverse Bits: `Reduction` (fold over 32 bit positions).

use super::{entry, gen};
use crate::candidates::Bisection;
use crate::config::CorpusEntry;
use crate::equivalence::Equiv;
use crate::primitives::{ActuationPass, PriorityQueue, Reduction, ResourceRegistry};
use crate::value::Value;
use std::cmp::Reverse;

// ──────────────────────────────────────────────────────────────────────────────
// Greedy
// ──────────────────────────────────────────────────────────────────────────────

// --- Maximum Subarray (Kadane's Algorithm) ---
// Two interleaved Reduction(max) passes: running best-ending-here,
// running best-overall. Structural ordering: Linear.
fn maximum_subarray(input: Value) -> Value {
    let a = input.as_int_vec();
    if a.is_empty() {
        return Value::Int(0);
    }
    // best_here: Reduction with conditional reset (start new subarray when negative)
    let mut best_here = a[0];
    let mut best_overall = a[0];
    for &x in &a[1..] {
        // Reduction: max(extend, start-fresh) — the "greedy reset" operator
        best_here = Reduction::reduce(vec![best_here + x, x], i64::MIN, |a, b| a.max(b));
        best_overall = Reduction::reduce(vec![best_overall, best_here], i64::MIN, |a, b| a.max(b));
    }
    Value::Int(best_overall)
}

// --- Jump Game ---
// Reduction(max) running furthest-reachable over the array; feasibility
// predicate at each step. Structural ordering: Linear.
fn jump_game(input: Value) -> Value {
    let a = input.as_int_vec();
    if a.is_empty() {
        return Value::Bool(true);
    }
    let n = a.len();
    let mut furthest: i64 = 0;
    for i in 0..n {
        if i as i64 > furthest {
            return Value::Bool(false);
        }
        furthest = Reduction::reduce(vec![furthest, i as i64 + a[i]], i64::MIN, |x, y| x.max(y));
    }
    Value::Bool(furthest >= (n as i64 - 1))
}

// --- Gas Station ---
// Two Reduction(sum) passes with shared running state: net-running-sum
// (with reset-candidate tracking) and total-net-sum (feasibility).
// Structural ordering: Linear.
fn gas_station(input: Value) -> Value {
    let parts = input.as_list();
    let gas = parts[0].as_int_vec();
    let cost = parts[1].as_int_vec();
    let n = gas.len();
    if n == 0 {
        return Value::Int(-1);
    }
    // Reduction(sum) total net — feasibility check
    let total_net = Reduction::reduce(
        gas.iter().zip(cost.iter()).map(|(&g, &c)| g - c),
        0i64,
        |a, b| a + b,
    );
    if total_net < 0 {
        return Value::Int(-1);
    }
    // Reduction(sum+reset) — find candidate start
    let mut net = 0i64;
    let mut start = 0usize;
    for i in 0..n {
        net = Reduction::reduce(vec![net, gas[i] - cost[i]], 0i64, |a, b| a + b);
        if net < 0 {
            start = i + 1;
            net = 0;
        }
    }
    Value::Int(start as i64)
}

// --- Hand of Straights ---
// SortThenSweep: (sort distinct cards) + ResourceRegistry (frequency counts).
// The order comes from the sort, so the smallest remaining card always starts
// the next group — no selection primitive is needed. Structural ordering: Linear.
fn hand_of_straights(input: Value) -> Value {
    let parts = input.as_list();
    let hand = parts[0].as_int_vec();
    let w = parts[1].as_int() as usize;
    if w == 0 {
        return Value::Bool(true);
    }
    if hand.len() % w != 0 {
        return Value::Bool(false);
    }
    // ResourceRegistry: card -> count
    let mut counts: ResourceRegistry<i64, i64> = ResourceRegistry::new();
    for &c in &hand {
        *counts.entry_or(c, 0) += 1;
    }
    // Sort distinct cards ascending: the smallest remaining card is always the
    // next group's start (the sort — not a selection primitive — gives the order).
    let mut keys: Vec<i64> = counts.keys().cloned().collect();
    keys.sort_unstable();

    for &k in &keys {
        let cnt = *counts.lookup(&k).unwrap_or(&0);
        if cnt == 0 {
            continue;
        }
        // Consume `cnt` groups of W consecutive cards starting at k.
        for j in 0..w as i64 {
            let need = k + j;
            let have = *counts.lookup(&need).unwrap_or(&0);
            if have < cnt {
                return Value::Bool(false);
            }
            counts.insert(need, have - cnt);
        }
    }
    Value::Bool(true)
}

// ──────────────────────────────────────────────────────────────────────────────
// Intervals
// ──────────────────────────────────────────────────────────────────────────────

/// Helper: extract [start, end] from a `Value::List([Int(s), Int(e)])`.
fn iv(v: &Value) -> (i64, i64) {
    let l = v.as_list();
    (l[0].as_int(), l[1].as_int())
}
/// Helper: encode interval pair back to Value.
fn iv_val(s: i64, e: i64) -> Value {
    Value::List(vec![Value::Int(s), Value::Int(e)])
}

// --- Merge Intervals ---
// Sort by start; Reduction over sorted sequence with merge-or-emit operator.
// Structural ordering: Tree (sort+scan sequential phases).
fn merge_intervals(input: Value) -> Value {
    let raw = input.as_list();
    if raw.is_empty() {
        return Value::List(vec![]);
    }
    let mut ivs: Vec<(i64, i64)> = raw.iter().map(iv).collect();
    ivs.sort_unstable();

    // Reduction: merge-or-emit operator over sorted intervals.
    // Reduction::reduce requires Item==Accumulator type, so a plain fold is
    // used here to support the Vec<(i64,i64)> accumulator over (i64,i64)
    // items — same algorithmic structure, different type shape.
    let merged: Vec<(i64, i64)> = ivs.into_iter().fold(Vec::new(), |mut acc, (s, e)| {
        if let Some(last) = acc.last_mut() {
            if s <= last.1 {
                last.1 = last.1.max(e);
                return acc;
            }
        }
        acc.push((s, e));
        acc
    });
    Value::List(merged.into_iter().map(|(s, e)| iv_val(s, e)).collect())
}

// --- Insert Interval ---
// Input: Value::List of existing intervals + trailing new interval.
// Reduction over three-phase linear scan (before / overlapping / after).
// Structural ordering: Linear.
fn insert_interval(input: Value) -> Value {
    let raw = input.as_list();
    if raw.is_empty() {
        return Value::List(vec![]);
    }
    // Last element is the new interval; everything before is the sorted list.
    let (new_iv, existing) = raw.split_last().unwrap();
    let (mut ns, mut ne) = iv(new_iv);

    // Reduction: three-phase state machine with merge-extend operator
    let mut result: Vec<(i64, i64)> = Vec::new();
    let mut inserted = false;
    for v in existing {
        let (s, e) = iv(v);
        if e < ns {
            // before new interval
            result.push((s, e));
        } else if s > ne {
            // after new interval — emit new if not yet done, then this one
            if !inserted {
                result.push((ns, ne));
                inserted = true;
            }
            result.push((s, e));
        } else {
            // overlapping: Reduction(min/max) to extend new interval
            ns = Reduction::reduce(vec![ns, s], i64::MAX, |a, b| a.min(b));
            ne = Reduction::reduce(vec![ne, e], i64::MIN, |a, b| a.max(b));
        }
    }
    if !inserted {
        result.push((ns, ne));
    }
    Value::List(result.into_iter().map(|(s, e)| iv_val(s, e)).collect())
}

// --- Non-overlapping Intervals ---
// Sort by end; Reduction(running count) with tracked last-kept-end-time.
// Returns minimum removals = total - max_kept. Structural ordering: Tree.
fn non_overlapping_intervals(input: Value) -> Value {
    let raw = input.as_list();
    if raw.is_empty() {
        return Value::Int(0);
    }
    let mut ivs: Vec<(i64, i64)> = raw.iter().map(iv).collect();
    ivs.sort_unstable_by_key(|&(_, e)| e);

    let n = ivs.len() as i64;
    // Reduction over sorted intervals: count kept; greedy keep if non-overlapping
    let (kept, _) = Reduction::reduce(ivs, (0i64, i64::MIN), |(kept, last_end), (s, e)| {
        if s >= last_end {
            (kept + 1, e)
        } else {
            (kept, last_end)
        }
    });
    Value::Int(n - kept)
}

// --- Meeting Rooms II ---
// Sort by start. PriorityQueue<Reverse<i64>> (min-heap of end times) as
// CompetitiveSelection::hard data structure. Tracks minimum rooms needed.
// Structural ordering: Linear.
fn meeting_rooms_ii(input: Value) -> Value {
    let raw = input.as_list();
    if raw.is_empty() {
        return Value::Int(0);
    }
    let mut ivs: Vec<(i64, i64)> = raw.iter().map(iv).collect();
    ivs.sort_unstable_by_key(|&(s, _)| s);

    // PriorityQueue<Reverse<i64>>: min-heap of earliest end-times (CompetitiveSelection-hard)
    let mut pq: PriorityQueue<Reverse<i64>> = PriorityQueue::new();
    let mut max_rooms = 0usize;
    for (s, e) in ivs {
        // CompetitiveSelection-hard: check if earliest-ending room is free
        if let Some(&Reverse(earliest_end)) = pq.peek() {
            if earliest_end <= s {
                pq.pop_best(); // reuse that room
            }
        }
        pq.push(Reverse(e));
        max_rooms = max_rooms.max(pq.len());
    }
    Value::Int(max_rooms as i64)
}

// ──────────────────────────────────────────────────────────────────────────────
// Math & Geometry
// ──────────────────────────────────────────────────────────────────────────────

// --- Rotate Image ---
// Two sequential ActuationPass phases: transpose then reverse each row.
// Input: Value::List of rows (each a Value::List of ints).
// Output: rotated matrix (same encoding). Structural ordering: Tree.
fn rotate_image(input: Value) -> Value {
    let rows = input.as_list();
    let n = rows.len();
    if n == 0 {
        return Value::List(vec![]);
    }
    let mut mat: Vec<Vec<i64>> = rows.iter().map(|r| r.as_int_vec()).collect();

    // ActuationPass 1: transpose — swap each upper-triangle (i, j) with (j, i).
    let pairs: Vec<(usize, usize)> = (0..n)
        .flat_map(|i| ((i + 1)..n).map(move |j| (i, j)))
        .collect();
    ActuationPass::apply_each(pairs, |(i, j)| {
        let tmp = mat[i][j];
        mat[i][j] = mat[j][i];
        mat[j][i] = tmp;
    });

    // ActuationPass 2: reverse each row.
    ActuationPass::apply(&mut mat, |row| row.reverse());

    Value::List(mat.into_iter().map(|r| Value::ints(&r)).collect())
}

// --- Spiral Matrix ---
// Bounded-state TraversalEngine walk: the four boundary positions (top,
// bottom, left, right) are cursor state, shrunk after each side. No Reduction.
// Input: Value::List of rows. Output: Value::List of ints. Ordering: Linear.
fn spiral_matrix(input: Value) -> Value {
    let rows = input.as_list();
    if rows.is_empty() {
        return Value::List(vec![]);
    }
    let mat: Vec<Vec<i64>> = rows.iter().map(|r| r.as_int_vec()).collect();
    let m = mat.len() as i64;
    let n = mat[0].len() as i64;

    let mut top = 0i64;
    let mut bottom = m - 1;
    let mut left = 0i64;
    let mut right = n - 1;
    let mut result: Vec<Value> = Vec::new();

    // TraversalEngine: walk the boundary, shrinking the four bound cursors after each side.
    while top <= bottom && left <= right {
        // Walk top row left→right
        for c in left..=right {
            result.push(Value::Int(mat[top as usize][c as usize]));
        }
        top += 1;
        // Walk right col top→bottom
        for r in top..=bottom {
            result.push(Value::Int(mat[r as usize][right as usize]));
        }
        right -= 1;
        // Walk bottom row right→left (if still valid)
        if top <= bottom {
            for c in (left..=right).rev() {
                result.push(Value::Int(mat[bottom as usize][c as usize]));
            }
            bottom -= 1;
        }
        // Walk left col bottom→top (if still valid)
        if left <= right {
            for r in (top..=bottom).rev() {
                result.push(Value::Int(mat[r as usize][left as usize]));
            }
            left += 1;
        }
    }
    Value::List(result)
}

// --- Set Matrix Zeroes ---
// Two ActuationPass phases: first marks flags, second applies zeros.
// Input/Output: matrix as Value::List of rows. Structural ordering: Tree.
fn set_matrix_zeroes(input: Value) -> Value {
    let rows = input.as_list();
    if rows.is_empty() {
        return Value::List(vec![]);
    }
    let mut mat: Vec<Vec<i64>> = rows.iter().map(|r| r.as_int_vec()).collect();
    let m = mat.len();
    let n = mat[0].len();

    let mut zero_rows: Vec<bool> = vec![false; m];
    let mut zero_cols: Vec<bool> = vec![false; n];
    let cells: Vec<(usize, usize)> = (0..m).flat_map(|i| (0..n).map(move |j| (i, j))).collect();

    // ActuationPass 1: scan cells, write row/col zero-flags.
    ActuationPass::apply_each(cells.clone(), |(i, j)| {
        if mat[i][j] == 0 {
            zero_rows[i] = true;
            zero_cols[j] = true;
        }
    });

    // ActuationPass 2: apply zeros from the flags.
    ActuationPass::apply_each(cells, |(i, j)| {
        if zero_rows[i] || zero_cols[j] {
            mat[i][j] = 0;
        }
    });

    Value::List(mat.into_iter().map(|r| Value::ints(&r)).collect())
}

// --- Pow(x, n) — fast exponentiation ---
// Bisection over the exponent's bit structure + Reduction(product)
// accumulating squared bases. INTEGER base, non-negative exponent, exact Int
// output. Structural ordering: Linear.
fn pow_xn(input: Value) -> Value {
    let parts = input.as_list();
    let base = parts[0].as_int();
    let exp = parts[1].as_int().max(0) as u64;

    if exp == 0 {
        return Value::Int(1);
    }

    // Bisection over the exponent's bit positions: locate the bit-length (the
    // smallest b with exp >> b == 0) by halving the [0, 63] range. This is the
    // halving structure of fast exponentiation — each bit halves the remaining
    // exponent magnitude.
    let bits = Bisection::first_true(0, 63, |b| (exp >> b) == 0).unwrap_or(64) as u64;

    // Reduction(product): accumulate squared bases over the bit positions.
    // Reduction::reduce requires Item==Accumulator type, so a plain fold is
    // used here to support the (i64,i64) accumulator over u64 bits.
    let (result, _): (i64, i64) = (0u64..bits).fold((1i64, base), |(acc, cur), bit| {
        let new_acc = if (exp >> bit) & 1 == 1 {
            acc.wrapping_mul(cur)
        } else {
            acc
        };
        let new_cur = cur.wrapping_mul(cur);
        (new_acc, new_cur)
    });
    Value::Int(result)
}

// --- Happy Number ---
// Floyd's tortoise-and-hare cycle detection on iterated digit-square-sum.
// The cycle detection is structural and uses no catalog primitive.
// Structural ordering: Linear.
fn happy_number(input: Value) -> Value {
    fn digit_sq_sum(mut n: i64) -> i64 {
        let mut s = 0i64;
        while n > 0 {
            let d = n % 10;
            s += d * d;
            n /= 10;
        }
        s
    }
    let mut n = input.as_int().abs().max(1);
    let mut slow = n;
    let mut fast = digit_sq_sum(n);
    while fast != 1 && slow != fast {
        slow = digit_sq_sum(slow);
        fast = digit_sq_sum(digit_sq_sum(fast));
    }
    let _ = n; // keep binding to avoid unused warning
    n = fast;
    Value::Bool(n == 1)
}

// ──────────────────────────────────────────────────────────────────────────────
// Bit Manipulation
// ──────────────────────────────────────────────────────────────────────────────

// --- Number of 1 Bits (Hamming Weight) ---
// Reduction(count) over a loop that strips one set bit per iteration
// (Kernighan: n & (n-1)). Structural ordering: Linear.
fn hamming_weight(input: Value) -> Value {
    let mut n = input.as_int() as u64;
    let count = Reduction::reduce(
        std::iter::from_fn(move || {
            if n == 0 {
                None
            } else {
                n &= n - 1; // clear lowest set bit
                Some(1i64)
            }
        }),
        0i64,
        |a, b| a + b,
    );
    Value::Int(count)
}

// --- Single Number ---
// Reduction under XOR: pairs cancel (a XOR a = 0), single survives.
// Structural ordering: Tree (XOR is commutative+associative).
fn single_number(input: Value) -> Value {
    let a = input.as_int_vec();
    Value::Int(Reduction::reduce(a, 0i64, |acc, x| acc ^ x))
}

// --- Missing Number ---
// Reduction under XOR over indices 0..=N and values: duplicates cancel,
// missing number survives. Structural ordering: Tree.
fn missing_number(input: Value) -> Value {
    let a = input.as_int_vec();
    let n = a.len() as i64;
    // XOR all indices 0..=n
    let idx_xor = Reduction::reduce(0..=n, 0i64, |acc, x| acc ^ x);
    // XOR all values
    let val_xor = Reduction::reduce(a, 0i64, |acc, x| acc ^ x);
    Value::Int(idx_xor ^ val_xor)
}

// --- Counting Bits ---
// Memoization = ResourceRegistry + Reduction (DAG via bit-shift relation).
// dp[i] = dp[i >> 1] + (i & 1). Structural ordering: DAG.
fn counting_bits(input: Value) -> Value {
    let n = input.as_int().max(0) as usize;
    let mut dp: ResourceRegistry<usize, i64> = ResourceRegistry::new();
    dp.insert(0, 0);
    for i in 1..=n {
        let parent = *dp.lookup(&(i >> 1)).unwrap();
        let bit = (i & 1) as i64;
        dp.insert(i, Reduction::reduce(vec![parent, bit], 0i64, |a, b| a + b));
    }
    let result: Vec<i64> = (0..=n).map(|i| *dp.lookup(&i).unwrap()).collect();
    Value::ints(&result)
}

// --- Reverse Bits ---
// Reduction: fold the 32 source bits into a shifted accumulator
// (acc = (acc<<1) | ((n>>bit)&1)), aligned with Number of 1 Bits.
// Structural ordering: Linear.
fn reverse_bits(input: Value) -> Value {
    let n = input.as_int() as u32;
    // Reduction (fold): bit `bit` of the input lands at position 31−bit.
    let result = Reduction::reduce(0..32u32, 0u32, |acc, bit| (acc << 1) | ((n >> bit) & 1));
    Value::Int(result as i64)
}

// ──────────────────────────────────────────────────────────────────────────────
// Input generators
// ──────────────────────────────────────────────────────────────────────────────

fn g_kadane() -> Vec<Value> {
    let mut v = vec![
        Value::ints(&[-2, 1, -3, 4, -1, 2, 1, -5, 4]),
        Value::ints(&[1]),
        Value::ints(&[5, 4, -1, 7, 8]),
        Value::ints(&[]),
        Value::ints(&[-1, -2, -3]),
    ];
    v.extend(gen::rand_int_lists(80, 1000, 12, -10, 10));
    v
}

fn g_jump() -> Vec<Value> {
    let mut v = vec![
        Value::ints(&[2, 3, 1, 1, 4]),
        Value::ints(&[3, 2, 1, 0, 4]),
        Value::ints(&[0]),
        Value::ints(&[]),
        Value::ints(&[1, 0]),
    ];
    v.extend(gen::rand_int_lists(81, 1000, 10, 0, 5));
    v
}

fn g_gas() -> Vec<Value> {
    let mut v = vec![
        Value::List(vec![
            Value::ints(&[1, 2, 3, 4, 5]),
            Value::ints(&[3, 4, 5, 1, 2]),
        ]),
        Value::List(vec![Value::ints(&[2, 3, 4]), Value::ints(&[3, 4, 3])]),
        Value::List(vec![Value::ints(&[]), Value::ints(&[])]),
    ];
    for i in 0..1000usize {
        let n = 1 + (i % 5);
        let gas: Vec<i64> = (0..n).map(|j| 1 + ((i + j) % 4) as i64).collect();
        let cost: Vec<i64> = (0..n).map(|j| 1 + ((i + j + 1) % 4) as i64).collect();
        v.push(Value::List(vec![Value::ints(&gas), Value::ints(&cost)]));
    }
    v
}

fn g_hand() -> Vec<Value> {
    let mut v = vec![
        Value::List(vec![
            Value::ints(&[1, 2, 3, 6, 2, 3, 4, 7, 8]),
            Value::Int(3),
        ]),
        Value::List(vec![Value::ints(&[1, 2, 3, 4, 5]), Value::Int(4)]),
        Value::List(vec![Value::ints(&[]), Value::Int(1)]),
        Value::List(vec![Value::ints(&[1, 2, 3]), Value::Int(3)]),
        Value::List(vec![Value::ints(&[1, 1, 2, 2, 3, 3]), Value::Int(3)]),
    ];
    for i in 0..1000usize {
        let w = 1 + (i % 3) as i64;
        let k = 1 + (i % 4) as i64;
        // Build k valid groups of w consecutive cards starting at (i%5)
        let start = (i % 5) as i64;
        let mut cards: Vec<i64> = Vec::new();
        for _g in 0..k {
            for j in 0..w {
                cards.push(start + j);
            }
        }
        v.push(Value::List(vec![Value::ints(&cards), Value::Int(w)]));
    }
    v
}

fn g_merge_iv() -> Vec<Value> {
    let make_iv = |s: i64, e: i64| Value::List(vec![Value::Int(s), Value::Int(e)]);
    let mut v = vec![
        Value::List(vec![
            make_iv(1, 3),
            make_iv(2, 6),
            make_iv(8, 10),
            make_iv(15, 18),
        ]),
        Value::List(vec![make_iv(1, 4), make_iv(4, 5)]),
        Value::List(vec![]),
        Value::List(vec![make_iv(1, 1)]),
    ];
    let mut s = crate::primitives::Sampler::new(90);
    for _ in 0..1000 {
        let k = 1 + s.pick_index(5);
        let ivs: Vec<Value> = (0..k)
            .map(|_| {
                let a = s.pick_index(20) as i64;
                let b = a + s.pick_index(5) as i64;
                make_iv(a, b)
            })
            .collect();
        v.push(Value::List(ivs));
    }
    v
}

fn g_insert_iv() -> Vec<Value> {
    let make_iv = |s: i64, e: i64| Value::List(vec![Value::Int(s), Value::Int(e)]);
    // Input: sorted non-overlapping intervals + trailing new interval
    let mut v = vec![
        Value::List(vec![make_iv(1, 3), make_iv(6, 9), make_iv(2, 5)]),
        Value::List(vec![
            make_iv(1, 2),
            make_iv(3, 5),
            make_iv(6, 7),
            make_iv(8, 10),
            make_iv(12, 16),
            make_iv(4, 8),
        ]),
        Value::List(vec![make_iv(0, 5)]), // only new interval
        Value::List(vec![make_iv(1, 5), make_iv(0, 0)]), // before all
    ];
    let mut s = crate::primitives::Sampler::new(91);
    for _ in 0..1000 {
        let k = s.pick_index(5);
        // Build sorted non-overlapping intervals
        let mut pos = 0i64;
        let mut ivs: Vec<Value> = Vec::new();
        for _ in 0..k {
            let start = pos + s.pick_index(3) as i64;
            let end = start + s.pick_index(4) as i64;
            ivs.push(make_iv(start, end));
            pos = end + 1 + s.pick_index(2) as i64;
        }
        // Append new interval to insert
        let new_s = s.pick_index(pos as usize + 5) as i64;
        let new_e = new_s + s.pick_index(5) as i64;
        ivs.push(make_iv(new_s, new_e));
        v.push(Value::List(ivs));
    }
    v
}

fn g_non_overlap() -> Vec<Value> {
    let make_iv = |s: i64, e: i64| Value::List(vec![Value::Int(s), Value::Int(e)]);
    let mut v = vec![
        Value::List(vec![
            make_iv(1, 2),
            make_iv(2, 3),
            make_iv(3, 4),
            make_iv(1, 3),
        ]),
        Value::List(vec![make_iv(1, 2), make_iv(1, 2), make_iv(1, 2)]),
        Value::List(vec![make_iv(1, 2), make_iv(2, 3)]),
        Value::List(vec![]),
    ];
    let mut s = crate::primitives::Sampler::new(92);
    for _ in 0..1000 {
        let k = 1 + s.pick_index(6);
        let ivs: Vec<Value> = (0..k)
            .map(|_| {
                let a = s.pick_index(10) as i64;
                let b = a + 1 + s.pick_index(4) as i64;
                make_iv(a, b)
            })
            .collect();
        v.push(Value::List(ivs));
    }
    v
}

fn g_meeting_rooms() -> Vec<Value> {
    let make_iv = |s: i64, e: i64| Value::List(vec![Value::Int(s), Value::Int(e)]);
    let mut v = vec![
        Value::List(vec![make_iv(0, 30), make_iv(5, 10), make_iv(15, 20)]),
        Value::List(vec![make_iv(7, 10), make_iv(2, 4)]),
        Value::List(vec![]),
        Value::List(vec![make_iv(1, 5)]),
    ];
    let mut s = crate::primitives::Sampler::new(93);
    for _ in 0..1000 {
        let k = 1 + s.pick_index(6);
        let ivs: Vec<Value> = (0..k)
            .map(|_| {
                let a = s.pick_index(20) as i64;
                let b = a + 1 + s.pick_index(10) as i64;
                make_iv(a, b)
            })
            .collect();
        v.push(Value::List(ivs));
    }
    v
}

fn g_rotate() -> Vec<Value> {
    let row = |v: &[i64]| Value::ints(v);
    let mut v = vec![
        Value::List(vec![row(&[1, 2, 3]), row(&[4, 5, 6]), row(&[7, 8, 9])]),
        Value::List(vec![
            row(&[5, 1, 9, 11]),
            row(&[2, 4, 8, 10]),
            row(&[13, 3, 6, 7]),
            row(&[15, 14, 12, 16]),
        ]),
        Value::List(vec![row(&[1])]),
        Value::List(vec![]),
    ];
    // Property: NxN matrices with N in 1..=5
    let mut s = crate::primitives::Sampler::new(94);
    for _ in 0..1000 {
        let n = 1 + s.pick_index(4);
        let rows: Vec<Value> = (0..n)
            .map(|_| {
                let cells: Vec<i64> = (0..n).map(|_| s.pick_index(100) as i64).collect();
                Value::ints(&cells)
            })
            .collect();
        v.push(Value::List(rows));
    }
    v
}

fn g_spiral() -> Vec<Value> {
    let row = |v: &[i64]| Value::ints(v);
    let mut v = vec![
        Value::List(vec![row(&[1, 2, 3]), row(&[4, 5, 6]), row(&[7, 8, 9])]),
        Value::List(vec![
            row(&[1, 2, 3, 4]),
            row(&[5, 6, 7, 8]),
            row(&[9, 10, 11, 12]),
        ]),
        Value::List(vec![row(&[1])]),
        Value::List(vec![]),
    ];
    let mut s = crate::primitives::Sampler::new(95);
    for _ in 0..1000 {
        let m = 1 + s.pick_index(4);
        let n = 1 + s.pick_index(4);
        let rows: Vec<Value> = (0..m)
            .map(|_| {
                let cells: Vec<i64> = (0..n).map(|_| s.pick_index(50) as i64).collect();
                Value::ints(&cells)
            })
            .collect();
        v.push(Value::List(rows));
    }
    v
}

fn g_set_zeros() -> Vec<Value> {
    let row = |v: &[i64]| Value::ints(v);
    let mut v = vec![
        Value::List(vec![row(&[1, 1, 1]), row(&[1, 0, 1]), row(&[1, 1, 1])]),
        Value::List(vec![
            row(&[0, 1, 2, 0]),
            row(&[3, 4, 5, 2]),
            row(&[1, 3, 1, 5]),
        ]),
        Value::List(vec![row(&[1])]),
        Value::List(vec![]),
    ];
    let mut s = crate::primitives::Sampler::new(96);
    for _ in 0..1000 {
        let m = 1 + s.pick_index(4);
        let n = 1 + s.pick_index(4);
        let rows: Vec<Value> = (0..m)
            .map(|_| {
                let cells: Vec<i64> = (0..n)
                    .map(|_| {
                        let x = s.pick_index(5) as i64;
                        if x == 0 {
                            0
                        } else {
                            x
                        }
                    })
                    .collect();
                Value::ints(&cells)
            })
            .collect();
        v.push(Value::List(rows));
    }
    v
}

fn g_pow() -> Vec<Value> {
    let mut v = vec![
        Value::List(vec![Value::Int(2), Value::Int(10)]),
        Value::List(vec![Value::Int(2), Value::Int(0)]),
        Value::List(vec![Value::Int(3), Value::Int(5)]),
        Value::List(vec![Value::Int(1), Value::Int(1000)]),
        Value::List(vec![Value::Int(0), Value::Int(5)]),
        Value::List(vec![Value::Int(-2), Value::Int(3)]),
        Value::List(vec![Value::Int(-3), Value::Int(4)]),
    ];
    for i in 0..1000usize {
        let base = (i % 7) as i64 - 3; // -3..3
        let exp = (i % 12) as i64;
        v.push(Value::List(vec![Value::Int(base), Value::Int(exp)]));
    }
    v
}

fn g_happy() -> Vec<Value> {
    let mut v = vec![
        Value::Int(19),
        Value::Int(2),
        Value::Int(1),
        Value::Int(7),
        Value::Int(100),
    ];
    v.extend(gen::rand_ints(97, 1000, 1000));
    v
}

fn g_hamming() -> Vec<Value> {
    let mut v = vec![
        Value::Int(11),  // 1011 -> 3
        Value::Int(128), // 10000000 -> 1
        Value::Int(0),
        Value::Int(u32::MAX as i64),
    ];
    v.extend(gen::rand_ints(98, 1000, u32::MAX as i64));
    v
}

fn g_single_number() -> Vec<Value> {
    let mut v = vec![
        Value::ints(&[2, 2, 1]),
        Value::ints(&[4, 1, 2, 1, 2]),
        Value::ints(&[1]),
    ];
    let mut s = crate::primitives::Sampler::new(99);
    for _ in 0..1000 {
        let unique = s.pick_index(100) as i64;
        let k = 1 + s.pick_index(5); // k pairs
        let mut a: Vec<i64> = vec![unique];
        for _ in 0..k {
            let x = s.pick_index(100) as i64;
            a.push(x);
            a.push(x);
        }
        // Fisher-Yates shuffle via Sampler
        for i in (1..a.len()).rev() {
            let j = s.pick_index(i + 1);
            a.swap(i, j);
        }
        v.push(Value::ints(&a));
    }
    v
}

fn g_missing_number() -> Vec<Value> {
    let mut v = vec![
        Value::ints(&[3, 0, 1]),
        Value::ints(&[0, 1]),
        Value::ints(&[9, 6, 4, 2, 3, 5, 7, 0, 1]),
        Value::ints(&[0]),
    ];
    let mut s = crate::primitives::Sampler::new(100);
    for _ in 0..1000 {
        let n = 1 + s.pick_index(15);
        let missing = s.pick_index(n + 1);
        let mut a: Vec<i64> = (0..=(n as i64)).filter(|&x| x != missing as i64).collect();
        // shuffle
        for i in (1..a.len()).rev() {
            let j = s.pick_index(i + 1);
            a.swap(i, j);
        }
        v.push(Value::ints(&a));
    }
    v
}

fn g_counting_bits() -> Vec<Value> {
    let mut v = vec![Value::Int(0), Value::Int(1), Value::Int(2), Value::Int(5)];
    v.extend(gen::rand_ints(101, 1000, 64));
    v
}

fn g_reverse_bits() -> Vec<Value> {
    let mut v = vec![
        Value::Int(43261596), // 00000010100101000001111010011100 -> 964176192
        Value::Int(u32::MAX as i64),
        Value::Int(0),
        Value::Int(1),
    ];
    v.extend(gen::rand_ints(102, 1000, u32::MAX as i64));
    v
}

pub fn add(r: &mut Vec<CorpusEntry>) {
    // Greedy
    let gr = "Reduction (running aggregate)";
    let hr = "SortThenSweep: (sort) + ResourceRegistry(card counts)";
    entry(
        r,
        "Maximum Subarray",
        "Greedy",
        8,
        "Linear",
        gr,
        maximum_subarray,
        "maximum_subarray",
        Equiv::Exact,
        g_kadane,
    );
    entry(
        r,
        "Jump Game",
        "Greedy",
        8,
        "Linear",
        gr,
        jump_game,
        "jump_game",
        Equiv::BoolEq,
        g_jump,
    );
    entry(
        r,
        "Gas Station",
        "Greedy",
        8,
        "Linear",
        gr,
        gas_station,
        "gas_station",
        Equiv::Exact,
        g_gas,
    );
    entry(
        r,
        "Hand of Straights",
        "Greedy",
        8,
        "Linear",
        hr,
        hand_of_straights,
        "hand_of_straights",
        Equiv::BoolEq,
        g_hand,
    );

    // Intervals
    let iv_r = "Reduction (merge-or-emit over sorted intervals)";
    let iv_pq = "PriorityQueue (CompetitiveSelection-hard, min-heap of end times)";
    entry(
        r,
        "Merge Intervals",
        "Intervals",
        8,
        "Tree",
        iv_r,
        merge_intervals,
        "merge_intervals",
        Equiv::Exact,
        g_merge_iv,
    );
    entry(
        r,
        "Insert Interval",
        "Intervals",
        8,
        "Linear",
        iv_r,
        insert_interval,
        "insert_interval",
        Equiv::Exact,
        g_insert_iv,
    );
    entry(
        r,
        "Non-overlapping Intervals",
        "Intervals",
        8,
        "Tree",
        iv_r,
        non_overlapping_intervals,
        "non_overlapping_intervals",
        Equiv::Exact,
        g_non_overlap,
    );
    entry(
        r,
        "Meeting Rooms II",
        "Intervals",
        8,
        "Linear",
        iv_pq,
        meeting_rooms_ii,
        "meeting_rooms_ii",
        Equiv::Exact,
        g_meeting_rooms,
    );

    // Math & Geometry
    let ap = "ActuationPass (two-pass in-place)";
    let bp = "Bisection (over exponent bits) + Reduction (product)";
    let tr = "TraversalEngine (bounded-state spiral walk; bounds are cursor state)";
    let cy = "Floyd cycle detection (structural; no catalog primitive)";
    entry(
        r,
        "Rotate Image",
        "Math & Geometry",
        8,
        "Tree",
        ap,
        rotate_image,
        "rotate_image",
        Equiv::Exact,
        g_rotate,
    );
    entry(
        r,
        "Spiral Matrix",
        "Math & Geometry",
        8,
        "Linear",
        tr,
        spiral_matrix,
        "spiral_matrix",
        Equiv::Exact,
        g_spiral,
    );
    entry(
        r,
        "Set Matrix Zeroes",
        "Math & Geometry",
        8,
        "Tree",
        ap,
        set_matrix_zeroes,
        "set_matrix_zeroes",
        Equiv::Exact,
        g_set_zeros,
    );
    entry(
        r,
        "Pow(x,n)",
        "Math & Geometry",
        8,
        "Linear",
        bp,
        pow_xn,
        "pow_xn",
        Equiv::Exact,
        g_pow,
    );
    entry(
        r,
        "Happy Number",
        "Math & Geometry",
        8,
        "Linear",
        cy,
        happy_number,
        "happy_number",
        Equiv::BoolEq,
        g_happy,
    );

    // Bit Manipulation
    let rx = "Reduction (XOR)";
    let rc = "Reduction (count over iterated bit-strip)";
    let mem = "Memoization = ResourceRegistry + Reduction (DAG: bit-shift dependency)";
    let acp = "Reduction (fold over 32 bit positions)";
    entry(
        r,
        "Number of 1 Bits",
        "Bit Manipulation",
        8,
        "Linear",
        rc,
        hamming_weight,
        "hamming_weight",
        Equiv::Exact,
        g_hamming,
    );
    entry(
        r,
        "Single Number",
        "Bit Manipulation",
        8,
        "Tree",
        rx,
        single_number,
        "single_number",
        Equiv::Exact,
        g_single_number,
    );
    entry(
        r,
        "Missing Number",
        "Bit Manipulation",
        8,
        "Tree",
        rx,
        missing_number,
        "missing_number",
        Equiv::Exact,
        g_missing_number,
    );
    entry(
        r,
        "Counting Bits",
        "Bit Manipulation",
        8,
        "DAG",
        mem,
        counting_bits,
        "counting_bits",
        Equiv::Exact,
        g_counting_bits,
    );
    entry(
        r,
        "Reverse Bits",
        "Bit Manipulation",
        8,
        "Linear",
        acp,
        reverse_bits,
        "reverse_bits",
        Equiv::Exact,
        g_reverse_bits,
    );
}
