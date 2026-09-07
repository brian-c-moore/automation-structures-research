//! Phase 2 — Stack + Binary Search.
//!
//! ## Stack — Structural ordering: **Linear**
//!
//! Composition pattern:
//!   - A LIFO / monotonic **stack is a substrate buffer** (a plain
//!     `Vec`), not a `ResourceRegistry`: a positionally-indexed buffer is
//!     not a unique key→value mapping, so it carries no governance
//!     invariant and is named structurally.
//!   - `ActuationPass` drives the eviction loop for the monotonic-stack
//!     algorithms.
//!   - `Reduction` computes the per-eviction answer (difference for
//!     Daily Temperatures; area for Largest Rectangle in Histogram).
//!
//! ## Binary Search — Structural ordering: **Linear**
//!
//! Composition pattern: all six algorithms are built **only** from
//! `candidates::Bisection` (plus `Reduction` for Koko's per-probe
//! feasibility sum).  No std sort, no raw binary-search loops.

use super::{entry, gen};
use crate::candidates::Bisection;
use crate::config::CorpusEntry;
use crate::equivalence::Equiv;
use crate::primitives::{ActuationPass, Reduction};
use crate::value::Value;

// ─────────────────────────────────────────────────────────────────────────────
// Valid Parentheses
//
// I/O: input  = Value::Str (bracket string, chars from "()[]{}")
//      output = Value::Bool
//
// Composition: a LIFO stack of pending closers (substrate buffer — a plain
//   Vec; a positional buffer, not a ResourceRegistry). Pairing predicate is
//   a domain function (match table). No governance primitive.
// ─────────────────────────────────────────────────────────────────────────────
fn valid_parentheses(input: Value) -> Value {
    let s: Vec<char> = input.as_str().chars().collect();
    let mut stack: Vec<i64> = Vec::new(); // substrate buffer (LIFO)

    for ch in &s {
        match ch {
            '(' => stack.push(')' as i64),
            '[' => stack.push(']' as i64),
            '{' => stack.push('}' as i64),
            c => match stack.pop() {
                Some(expected) if *c as i64 == expected => {}
                _ => return Value::Bool(false),
            },
        }
    }
    Value::Bool(stack.is_empty())
}

// ─────────────────────────────────────────────────────────────────────────────
// Min Stack  (op / result sequence)
//
// I/O: input  = Value::List of ops, each Value::List([op_code, arg])
//        op_code 0 = push(arg), 1 = pop, 2 = top, 3 = getMin
//      output = Value::List of results for op_code 2 (top) and 3 (getMin).
//        ops 0 and 1 produce no output entry; ops 2/3 produce Value::Int.
//
// The test harness calls the Rust composition and the Python oracle with the
// same op sequence and compares the result lists.
//
// Composition: main + running-min stacks, both substrate buffers (plain
//   Vecs, not registries). Each push records Reduction(min){new_val,
//   current_min} on the min stack; each pop removes from both.
// ─────────────────────────────────────────────────────────────────────────────
fn min_stack(input: Value) -> Value {
    let ops = input.as_list();
    let mut main: Vec<i64> = Vec::new(); // substrate buffer
    let mut mins: Vec<i64> = Vec::new(); // substrate buffer (running min)
    let mut results: Vec<Value> = Vec::new();

    for op in ops {
        let pair = op.as_list();
        let code = pair[0].as_int();
        let arg = pair[1].as_int();
        match code {
            0 => {
                // push(arg): update both stacks
                let new_min = match mins.last() {
                    None => arg,
                    Some(&cur) => Reduction::reduce(vec![arg, cur], i64::MAX, |a, b| a.min(b)),
                };
                main.push(arg);
                mins.push(new_min);
            }
            1 => {
                main.pop();
                mins.pop();
            }
            2 => {
                if let Some(&v) = main.last() {
                    results.push(Value::Int(v));
                }
            }
            3 => {
                if let Some(&v) = mins.last() {
                    results.push(Value::Int(v));
                }
            }
            _ => {}
        }
    }
    Value::List(results)
}

// ─────────────────────────────────────────────────────────────────────────────
// Evaluate Reverse Polish Notation
//
// I/O: input  = Value::List of Value::Str tokens (digits and "+","-","*","/")
//      output = Value::Int
//
// Composition: an operand stack (substrate buffer — a plain Vec) +
//   Reduction (per-operator, fixed-arity: pop 2 operands, apply op, push).
// ─────────────────────────────────────────────────────────────────────────────
fn eval_rpn(input: Value) -> Value {
    let tokens = input.as_list();
    let mut stack: Vec<i64> = Vec::new(); // substrate buffer (operands)

    for tok in tokens {
        let s = tok.as_str();
        match s {
            "+" | "-" | "*" | "/" => {
                let b = stack.pop().unwrap();
                let a = stack.pop().unwrap();
                let result = Reduction::reduce(
                    vec![(a, b)],
                    (a, b), // identity irrelevant: exactly one element
                    |_, pair| match s {
                        "+" => (pair.0 + pair.1, 0),
                        "-" => (pair.0 - pair.1, 0),
                        "*" => (pair.0 * pair.1, 0),
                        "/" => (pair.0 / pair.1, 0),
                        _ => unreachable!(),
                    },
                )
                .0;
                stack.push(result);
            }
            num => stack.push(num.parse::<i64>().unwrap()),
        }
    }
    Value::Int(stack[0])
}

// ─────────────────────────────────────────────────────────────────────────────
// Daily Temperatures
//
// I/O: input  = Value::List of Value::Int (temperatures)
//      output = Value::List of Value::Int (days-until-warmer, 0 if none)
//
// Composition: a monotonic stack of pending (index, temp) pairs (substrate
//   buffer — a plain Vec) + ActuationPass (eviction loop: for each
//   temperature, evict all top entries whose temperature is exceeded) +
//   Reduction (per-eviction answer = current_index − evicted_index).
// ─────────────────────────────────────────────────────────────────────────────
fn daily_temperatures(input: Value) -> Value {
    let temps = input.as_int_vec();
    let n = temps.len();
    let mut ans = vec![0i64; n];
    // monotonic stack (substrate buffer): (index, temp)
    let mut stack: Vec<(i64, i64)> = Vec::new();

    for i in 0..n {
        let cur = temps[i];
        // Collect the entries to evict (temp < cur), popping the buffer.
        let mut evicted: Vec<i64> = Vec::new(); // evicted indices
        while let Some(&(idx, t)) = stack.last() {
            if t < cur {
                evicted.push(idx);
                stack.pop();
            } else {
                break;
            }
        }
        // ActuationPass: emit each evicted entry's answer via Reduction.
        ActuationPass::apply_each(evicted, |idx| {
            // Reduction: answer = i - idx = fold sum over [i, -idx].
            let days = Reduction::reduce(vec![i as i64, -idx], 0i64, |a, b| a + b);
            ans[idx as usize] = days;
        });
        stack.push((i as i64, cur));
    }
    Value::List(ans.into_iter().map(Value::Int).collect())
}

// ─────────────────────────────────────────────────────────────────────────────
// Largest Rectangle in Histogram
//
// I/O: input  = Value::List of Value::Int (bar heights)
//      output = Value::Int (max area)
//
// Composition: a monotonic stack of (start_idx, height) pairs (substrate
//   buffer — a plain Vec) + ActuationPass (eviction loop) + Reduction
//   (per-eviction area = height × width; running max).
//
// Sentinel: append height=0 to flush all pending bars at the end.
// ─────────────────────────────────────────────────────────────────────────────
fn largest_rect_histogram(input: Value) -> Value {
    let mut heights = input.as_int_vec();
    heights.push(0); // sentinel flush
    let n = heights.len();

    let mut stack: Vec<(i64, i64)> = Vec::new(); // substrate buffer: (start_idx, height)
    let mut max_area: i64 = 0;

    for i in 0..n {
        let cur_h = heights[i];
        let mut start = i as i64;

        // Evict entries with height >= cur_h, popping the buffer.
        let mut to_evict: Vec<(i64, i64)> = Vec::new(); // (start_idx, height)
        while let Some(&(s_idx, h)) = stack.last() {
            if h >= cur_h {
                to_evict.push((s_idx, h));
                stack.pop();
            } else {
                break;
            }
        }
        // ActuationPass: per eviction, Reduction(area = h × width) + running max.
        ActuationPass::apply_each(to_evict, |(s_idx, h)| {
            let area = Reduction::reduce(
                vec![(h, i as i64, s_idx)],
                (0i64, 0i64, 0i64),
                |_, (height, right, left)| (height * (right - left), 0, 0),
            )
            .0;
            max_area = max_area.max(area);
            start = s_idx; // extend leftward
        });
        if cur_h > 0 {
            stack.push((start, cur_h));
        }
    }
    Value::Int(max_area)
}

// ─────────────────────────────────────────────────────────────────────────────
// Binary Search
//
// I/O: input  = Value::List([sorted_list, target])
//      output = Value::Int (index, or -1)
//
// Primitives: Bisection::search
// ─────────────────────────────────────────────────────────────────────────────
fn binary_search(input: Value) -> Value {
    let p = input.as_list();
    let arr = p[0].as_int_vec();
    let target = p[1].as_int();
    let idx = Bisection::search(&arr, &target)
        .map(|i| i as i64)
        .unwrap_or(-1);
    Value::Int(idx)
}

// ─────────────────────────────────────────────────────────────────────────────
// Search in Rotated Sorted Array
//
// I/O: input  = Value::List([rotated_sorted_list, target])
//      output = Value::Int (index, or -1)
//
// Primitives: Bisection::first_true with composite predicate.
//   Strategy: find pivot (leftmost index where arr[i] <= arr[last]),
//   then binary search the correct half.
// ─────────────────────────────────────────────────────────────────────────────
fn search_rotated(input: Value) -> Value {
    let p = input.as_list();
    let arr = p[0].as_int_vec();
    let target = p[1].as_int();
    let n = arr.len();
    if n == 0 {
        return Value::Int(-1);
    }

    // Step 1: find rotation pivot using Bisection.
    // Predicate: arr[mid] <= arr[n-1]  (true = in the post-rotation segment)
    let last = arr[n - 1];
    let pivot = Bisection::first_true(0, n as i64 - 1, |mid| arr[mid as usize] <= last)
        .unwrap_or(n as i64) as usize;

    // Step 2: determine which sorted segment contains the target.
    let (lo, hi) = if target >= arr[0] && pivot > 0 {
        (0, pivot - 1)
    } else {
        (pivot, n - 1)
    };

    // Step 3: standard binary search in that segment via Bisection.
    let slice = &arr[lo..=hi];
    match Bisection::search(slice, &target) {
        Some(rel_idx) => Value::Int((lo + rel_idx) as i64),
        None => Value::Int(-1),
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Find Minimum in Rotated Sorted Array
//
// I/O: input  = Value::List of Value::Int (rotated sorted, no duplicates)
//      output = Value::Int (minimum value)
//
// Primitives: Bisection::first_true
//   Predicate: arr[mid] <= arr[n-1] → in post-rotation segment (min is here
//   or to the left of the boundary).
// ─────────────────────────────────────────────────────────────────────────────
fn find_min_rotated(input: Value) -> Value {
    let arr = input.as_int_vec();
    let n = arr.len();
    if n == 0 {
        return Value::Int(0);
    }
    let last = arr[n - 1];
    // pivot = leftmost index where arr[i] <= arr[n-1]
    let pivot = Bisection::first_true(0, n as i64 - 1, |mid| arr[mid as usize] <= last).unwrap_or(0)
        as usize;
    Value::Int(arr[pivot])
}

// ─────────────────────────────────────────────────────────────────────────────
// Koko Eating Bananas
//
// I/O: input  = Value::List([piles_list, h])
//        piles_list: List of Int, h: Int (hours available)
//      output = Value::Int (minimum eating rate k)
//
// Primitives:
//   - Bisection::first_true over rate domain [1, max_pile].
//   - Reduction (sum of ⌈pile/rate⌉) per probe.
// ─────────────────────────────────────────────────────────────────────────────
fn koko_bananas(input: Value) -> Value {
    let p = input.as_list();
    let piles = p[0].as_int_vec();
    let h = p[1].as_int();
    if piles.is_empty() {
        return Value::Int(1);
    }
    let max_pile = Reduction::reduce(piles.iter().cloned(), 0, |a, b| a.max(b));

    let rate = Bisection::first_true(1, max_pile, |k| {
        // Per-probe feasibility: Reduction(sum of ceil(pile/k)) <= h
        let total_hours = Reduction::reduce(
            piles.iter().map(|&pile| (pile + k - 1) / k),
            0i64,
            |a, b| a + b,
        );
        total_hours <= h
    });
    Value::Int(rate.unwrap_or(max_pile))
}

// ─────────────────────────────────────────────────────────────────────────────
// Median of Two Sorted Arrays
//
// I/O: input  = Value::List([list_a, list_b])
//        list_a, list_b: sorted List of Int
//      output = Value::Int (median × 2, to avoid floats, matching oracle)
//
// NOTE ON ENCODING: Both Rust and Python return `2 × median` as an integer
// (multiply before dividing) so that the exact comparison works without
// floating point. The oracle must use the same encoding.
//
// Primitives: Bisection::first_true over partition position in the smaller
//   array. The predicate checks: all elements left of partition ≤ all
//   elements right of partition.
// ─────────────────────────────────────────────────────────────────────────────
fn median_two_sorted(input: Value) -> Value {
    let p = input.as_list();
    let a = p[0].as_int_vec();
    let b = p[1].as_int_vec();
    // Ensure a is the smaller array (Bisection domain is smaller)
    let (a, b) = if a.len() <= b.len() { (a, b) } else { (b, a) };
    let (m, n) = (a.len(), b.len());
    let total = m + n;
    let half = (total + 1) / 2; // number of elements on the left side

    // Bisect over i in [0, m]: how many elements from `a` are on the left.
    // j = half - i elements from `b` are on the left.
    //
    // Monotone predicate (increasing in i):
    //   "b[j-1] <= a[i]"
    //   As i increases, a[i] increases (sorted), making this more likely true.
    //   The target is the SMALLEST i where b[j-1] <= a[i], and a[i-1] <= b[j]
    //   must also hold at the found point.
    //
    // Strategy: first_true on "b[j-1] <= a[i]" yields the smallest valid i.
    // At that i, the left partition is correctly balanced.
    let i = Bisection::first_true(0, m as i64, |ii| {
        let ii = ii as usize;
        let jj = half.saturating_sub(ii);
        // b[j-1] <= a[i]: left side of b does not exceed right side of a
        let b_left = if jj > 0 && jj <= n {
            b[jj - 1]
        } else {
            i64::MIN
        };
        let a_right = if ii < m { a[ii] } else { i64::MAX };
        b_left <= a_right
    })
    .unwrap_or(m as i64) as usize;

    let j = half.saturating_sub(i);

    let max_left = {
        let al = if i > 0 { a[i - 1] } else { i64::MIN };
        let bl = if j > 0 { b[j - 1] } else { i64::MIN };
        al.max(bl)
    };
    let min_right = {
        let ar = if i < m { a[i] } else { i64::MAX };
        let br = if j < n { b[j] } else { i64::MAX };
        ar.min(br)
    };

    // Return 2 × median to keep result as integer (see encoding note above).
    if total % 2 == 1 {
        Value::Int(max_left * 2)
    } else {
        Value::Int(max_left + min_right)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Input generators
// ─────────────────────────────────────────────────────────────────────────────

fn g_valid_parens() -> Vec<Value> {
    let mut v = vec![
        Value::Str("()".into()),
        Value::Str("()[]{}".into()),
        Value::Str("(]".into()),
        Value::Str("([)]".into()),
        Value::Str("{[]}".into()),
        Value::Str("".into()),
        Value::Str("(((".into()),
        Value::Str(")))".into()),
        Value::Str("()()()".into()),
        Value::Str("((()))".into()),
    ];
    // Property: generate random bracket strings
    use crate::primitives::Sampler;
    let mut s = Sampler::new(50);
    let pairs: &[(&str, &str)] = &[("(", ")"), ("[", "]"), ("{", "}")];
    for _ in 0..1000 {
        let len = 2 + s.pick_index(10) * 2;
        let chars: String = (0..len)
            .map(|_| {
                let p = s.pick_index(3);
                let side = s.pick_index(2);
                if side == 0 {
                    pairs[p].0
                } else {
                    pairs[p].1
                }
            })
            .collect::<Vec<_>>()
            .join("");
        v.push(Value::Str(chars));
    }
    v
}

fn g_min_stack() -> Vec<Value> {
    // Build random op sequences. Op: [code, arg]
    // code 0=push, 1=pop, 2=top, 3=getMin
    use crate::primitives::Sampler;
    let make_seq = |ops: &[&[i64]]| {
        Value::List(
            ops.iter()
                .map(|op| Value::List(vec![Value::Int(op[0]), Value::Int(op[1])]))
                .collect(),
        )
    };
    let mut v = vec![
        // push -2, push 0, push -3, getMin(=-3), pop, top(=0), getMin(=-2)
        make_seq(&[
            &[0, -2],
            &[0, 0],
            &[0, -3],
            &[3, 0],
            &[1, 0],
            &[2, 0],
            &[3, 0],
        ]),
        // push 5, getMin(=5), push 3, getMin(=3), pop, getMin(=5)
        make_seq(&[&[0, 5], &[3, 0], &[0, 3], &[3, 0], &[1, 0], &[3, 0]]),
    ];
    let mut s = Sampler::new(60);
    for _ in 0..1000 {
        let len = 3 + s.pick_index(12);
        let mut depth = 0usize;
        let mut ops: Vec<Value> = Vec::new();
        for _ in 0..len {
            let code = if depth == 0 {
                0
            } else {
                s.pick_index(4) as i64
            };
            let arg = if code == 0 {
                s.pick_index(20) as i64 - 10
            } else {
                0
            };
            ops.push(Value::List(vec![Value::Int(code), Value::Int(arg)]));
            match code {
                0 => depth += 1,
                1 => {
                    depth -= 1;
                }
                _ => {}
            }
        }
        v.push(Value::List(ops));
    }
    v
}

fn g_eval_rpn() -> Vec<Value> {
    let toks = |ts: &[&str]| Value::List(ts.iter().map(|t| Value::Str(t.to_string())).collect());
    let mut v = vec![
        toks(&["2", "1", "+", "3", "*"]),  // (2+1)*3 = 9
        toks(&["4", "13", "5", "/", "+"]), // 4 + 13/5 = 6
        toks(&[
            "10", "6", "9", "3", "+", "-11", "*", "/", "*", "17", "+", "5", "+",
        ]),
        toks(&["3"]),
        toks(&["2", "3", "*", "4", "+"]), // 10
    ];
    use crate::primitives::Sampler;
    let mut s = Sampler::new(70);
    let ops = ["+", "-", "*"];
    for _ in 0..1000 {
        let n_vals = 2 + s.pick_index(4); // 2..5 values
        let mut tokens: Vec<String> = Vec::new();
        // Push n_vals operands, n_vals-1 operators (always valid RPN)
        for j in 0..n_vals {
            tokens.push((s.pick_index(9) as i64 + 1).to_string());
            if j > 0 {
                tokens.push(ops[s.pick_index(3)].to_string());
            }
        }
        v.push(Value::List(
            tokens.iter().map(|t| Value::Str(t.clone())).collect(),
        ));
    }
    v
}

fn g_daily_temps() -> Vec<Value> {
    let mut v = vec![
        Value::ints(&[73, 74, 75, 71, 69, 72, 76, 73]),
        Value::ints(&[30, 40, 50, 60]),
        Value::ints(&[30, 60, 90]),
        Value::ints(&[]),
        Value::ints(&[90, 80, 70, 60]),
    ];
    v.extend(gen::rand_int_lists(80, 1000, 12, 30, 100));
    v
}

fn g_histogram() -> Vec<Value> {
    let mut v = vec![
        Value::ints(&[2, 1, 5, 6, 2, 3]),
        Value::ints(&[2, 4]),
        Value::ints(&[]),
        Value::ints(&[1]),
        Value::ints(&[5, 5, 5, 5]),
        Value::ints(&[1, 2, 3, 4, 5]),
        Value::ints(&[5, 4, 3, 2, 1]),
    ];
    v.extend(gen::rand_int_lists(90, 1000, 10, 0, 10));
    v
}

fn g_binary_search() -> Vec<Value> {
    let mut v = vec![
        Value::List(vec![Value::ints(&[-1, 0, 3, 5, 9, 12]), Value::Int(9)]),
        Value::List(vec![Value::ints(&[-1, 0, 3, 5, 9, 12]), Value::Int(2)]),
        Value::List(vec![Value::ints(&[]), Value::Int(0)]),
        Value::List(vec![Value::ints(&[5]), Value::Int(5)]),
        Value::List(vec![Value::ints(&[5]), Value::Int(6)]),
    ];
    use crate::primitives::Sampler;
    let mut s = Sampler::new(100);
    for _ in 0..1000 {
        let len = s.pick_index(12);
        let mut arr: Vec<i64> = (0..len).map(|_| s.pick_index(30) as i64).collect();
        arr.sort_unstable();
        arr.dedup();
        let target = if arr.is_empty() || s.pick_index(2) == 0 {
            s.pick_index(30) as i64
        } else {
            arr[s.pick_index(arr.len())]
        };
        v.push(Value::List(vec![Value::ints(&arr), Value::Int(target)]));
    }
    v
}

fn g_search_rotated() -> Vec<Value> {
    let mut v = vec![
        Value::List(vec![Value::ints(&[4, 5, 6, 7, 0, 1, 2]), Value::Int(0)]),
        Value::List(vec![Value::ints(&[4, 5, 6, 7, 0, 1, 2]), Value::Int(3)]),
        Value::List(vec![Value::ints(&[1]), Value::Int(0)]),
        Value::List(vec![Value::ints(&[1, 3]), Value::Int(3)]),
        Value::List(vec![Value::ints(&[3, 1]), Value::Int(1)]),
    ];
    use crate::primitives::Sampler;
    let mut s = Sampler::new(110);
    for _ in 0..1000 {
        let len = 1 + s.pick_index(10);
        let mut arr: Vec<i64> = {
            let mut a: Vec<i64> = (0..len).map(|_| s.pick_index(20) as i64).collect();
            a.sort_unstable();
            a.dedup();
            a
        };
        // rotate
        if !arr.is_empty() {
            let rot = s.pick_index(arr.len());
            arr.rotate_left(rot);
        }
        let target = if arr.is_empty() || s.pick_index(2) == 0 {
            s.pick_index(20) as i64
        } else {
            arr[s.pick_index(arr.len())]
        };
        v.push(Value::List(vec![Value::ints(&arr), Value::Int(target)]));
    }
    v
}

fn g_find_min_rotated() -> Vec<Value> {
    let mut v = vec![
        Value::ints(&[3, 4, 5, 1, 2]),
        Value::ints(&[4, 5, 6, 7, 0, 1, 2]),
        Value::ints(&[11, 13, 15, 17]),
        Value::ints(&[1]),
        Value::ints(&[2, 1]),
    ];
    use crate::primitives::Sampler;
    let mut s = Sampler::new(120);
    for _ in 0..1000 {
        let len = 1 + s.pick_index(10);
        let mut arr: Vec<i64> = {
            let mut a: Vec<i64> = (0..len as i64).map(|x| x * 2).collect();
            // permute by picking unique values
            let start: i64 = s.pick_index(20) as i64;
            a = a.iter().map(|&x| x + start).collect();
            a
        };
        if !arr.is_empty() {
            let rot = s.pick_index(arr.len());
            arr.rotate_left(rot);
        }
        v.push(Value::ints(&arr));
    }
    v
}

fn g_koko() -> Vec<Value> {
    let mut v = vec![
        Value::List(vec![Value::ints(&[3, 6, 7, 11]), Value::Int(8)]),
        Value::List(vec![Value::ints(&[30, 11, 23, 4, 20]), Value::Int(5)]),
        Value::List(vec![Value::ints(&[30, 11, 23, 4, 20]), Value::Int(6)]),
        Value::List(vec![Value::ints(&[1]), Value::Int(1)]),
        Value::List(vec![Value::ints(&[1, 1, 1, 1]), Value::Int(4)]),
    ];
    use crate::primitives::Sampler;
    let mut s = Sampler::new(130);
    for _ in 0..1000 {
        let len = 1 + s.pick_index(8);
        let piles: Vec<i64> = (0..len).map(|_| 1 + s.pick_index(20) as i64).collect();
        let h = len as i64 + s.pick_index(len * 3 + 1) as i64;
        v.push(Value::List(vec![Value::ints(&piles), Value::Int(h)]));
    }
    v
}

fn g_median_two() -> Vec<Value> {
    let mut v = vec![
        Value::List(vec![Value::ints(&[1, 3]), Value::ints(&[2])]),
        Value::List(vec![Value::ints(&[1, 2]), Value::ints(&[3, 4])]),
        Value::List(vec![Value::ints(&[0, 0]), Value::ints(&[0, 0])]),
        Value::List(vec![Value::ints(&[]), Value::ints(&[1])]),
        Value::List(vec![Value::ints(&[2]), Value::ints(&[])]),
        Value::List(vec![Value::ints(&[1, 2, 3]), Value::ints(&[4, 5, 6])]),
    ];
    use crate::primitives::Sampler;
    let mut s = Sampler::new(140);
    for _ in 0..1000 {
        let la = s.pick_index(8);
        let lb = s.pick_index(8);
        let mut a: Vec<i64> = (0..la).map(|_| s.pick_index(20) as i64).collect();
        let mut b: Vec<i64> = (0..lb).map(|_| s.pick_index(20) as i64).collect();
        a.sort_unstable();
        b.sort_unstable();
        v.push(Value::List(vec![Value::ints(&a), Value::ints(&b)]));
    }
    v
}

// ─────────────────────────────────────────────────────────────────────────────
// Registry
// ─────────────────────────────────────────────────────────────────────────────
pub fn add(r: &mut Vec<CorpusEntry>) {
    let ms = "monotonic stack (substrate buffer) + ActuationPass(evict) + Reduction";
    let bs = "Bisection";
    let bsr = "Bisection + Reduction(feasibility sum)";

    entry(
        r,
        "Valid Parentheses",
        "Stack",
        2,
        "Linear",
        "LIFO stack (substrate buffer)",
        valid_parentheses,
        "valid_parentheses",
        Equiv::BoolEq,
        g_valid_parens,
    );

    entry(
        r,
        "Min Stack",
        "Stack",
        2,
        "Linear",
        "main + running-min stacks (substrate buffers) + Reduction(min)",
        min_stack,
        "min_stack",
        Equiv::Exact,
        g_min_stack,
    );

    entry(
        r,
        "Evaluate Reverse Polish Notation",
        "Stack",
        2,
        "Linear",
        "operand stack (substrate buffer) + Reduction",
        eval_rpn,
        "eval_rpn",
        Equiv::Exact,
        g_eval_rpn,
    );

    entry(
        r,
        "Daily Temperatures",
        "Stack",
        2,
        "Linear",
        ms,
        daily_temperatures,
        "daily_temperatures",
        Equiv::Exact,
        g_daily_temps,
    );

    entry(
        r,
        "Largest Rectangle in Histogram",
        "Stack",
        2,
        "Linear",
        ms,
        largest_rect_histogram,
        "largest_rect_histogram",
        Equiv::Exact,
        g_histogram,
    );

    entry(
        r,
        "Binary Search",
        "Binary Search",
        2,
        "Linear",
        bs,
        binary_search,
        "binary_search",
        Equiv::Exact,
        g_binary_search,
    );

    entry(
        r,
        "Search in Rotated Sorted Array",
        "Binary Search",
        2,
        "Linear",
        bs,
        search_rotated,
        "search_rotated",
        Equiv::Exact,
        g_search_rotated,
    );

    entry(
        r,
        "Find Minimum in Rotated Sorted Array",
        "Binary Search",
        2,
        "Linear",
        bs,
        find_min_rotated,
        "find_min_rotated",
        Equiv::Exact,
        g_find_min_rotated,
    );

    entry(
        r,
        "Koko Eating Bananas",
        "Binary Search",
        2,
        "Linear",
        bsr,
        koko_bananas,
        "koko_bananas",
        Equiv::Exact,
        g_koko,
    );

    entry(
        r,
        "Median of Two Sorted Arrays",
        "Binary Search",
        2,
        "Linear",
        bs,
        median_two_sorted,
        "median_two_sorted",
        Equiv::Exact,
        g_median_two,
    );
}
