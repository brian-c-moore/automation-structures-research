//! Phase 1 — Dynamic Programming, one-dimensional and two-dimensional.
//!
//! Every algorithm here is the **Memoization composition**: a
//! `ResourceRegistry` table, filled in topological order over the
//! dependency relation (the `TraversalEngine` role — the loop order
//! respects the DAG), each cell a `Reduction` over its predecessors.
//! Structural ordering: **DAG**. Built only from the shared primitives.

use super::{entry, gen};
use crate::config::CorpusEntry;
use crate::equivalence::Equiv;
use crate::primitives::{Reduction, ResourceRegistry};
use crate::value::Value;

const INF: i64 = 1 << 60;

// --- Climbing Stairs : dp[i] = Reduction(+){dp[i-1], dp[i-2]} ---
fn climbing_stairs(input: Value) -> Value {
    let n = input.as_int().max(0) as usize;
    let mut dp: ResourceRegistry<usize, i64> = ResourceRegistry::new();
    dp.insert(0, 1);
    if n >= 1 {
        dp.insert(1, 1);
    }
    for i in 2..=n {
        let preds = vec![*dp.lookup(&(i - 1)).unwrap(), *dp.lookup(&(i - 2)).unwrap()];
        dp.insert(i, Reduction::reduce(preds, 0, |a, b| a + b));
    }
    Value::Int(*dp.lookup(&n).unwrap())
}

// --- House Robber : dp[i] = Reduction(max){skip, take} ---
fn house_robber(input: Value) -> Value {
    let a = input.as_int_vec();
    if a.is_empty() {
        return Value::Int(0);
    }
    let mut dp: ResourceRegistry<usize, i64> = ResourceRegistry::new();
    for i in 0..a.len() {
        let skip = if i == 0 {
            0
        } else {
            *dp.lookup(&(i - 1)).unwrap()
        };
        let take = if i >= 2 {
            *dp.lookup(&(i - 2)).unwrap()
        } else {
            0
        } + a[i];
        dp.insert(
            i,
            Reduction::reduce(vec![skip, take], i64::MIN, |x, y| x.max(y)),
        );
    }
    Value::Int(*dp.lookup(&(a.len() - 1)).unwrap())
}

// --- Longest Increasing Subsequence (O(n^2) DP) ---
fn lis(input: Value) -> Value {
    let a = input.as_int_vec();
    if a.is_empty() {
        return Value::Int(0);
    }
    let mut dp: ResourceRegistry<usize, i64> = ResourceRegistry::new();
    let mut best = 0i64;
    for i in 0..a.len() {
        let cands: Vec<i64> = (0..i)
            .filter(|&j| a[j] < a[i])
            .map(|j| *dp.lookup(&j).unwrap())
            .collect();
        let v = 1 + Reduction::reduce(cands, 0, |x, y| x.max(y));
        dp.insert(i, v);
        best = best.max(v);
    }
    Value::Int(best)
}

// --- Coin Change : dp[v] = Reduction(min){dp[v-c]+1} ---
fn coin_change(input: Value) -> Value {
    let parts = input.as_list();
    let coins = parts[0].as_int_vec();
    let amount = parts[1].as_int() as usize;
    let mut dp: ResourceRegistry<usize, i64> = ResourceRegistry::new();
    dp.insert(0, 0);
    for v in 1..=amount {
        let cands: Vec<i64> = coins
            .iter()
            .filter(|&&c| c > 0 && (c as usize) <= v)
            .map(|&c| {
                let p = *dp.lookup(&(v - c as usize)).unwrap_or(&INF);
                if p >= INF {
                    INF
                } else {
                    p + 1
                }
            })
            .collect();
        dp.insert(v, Reduction::reduce(cands, INF, |x, y| x.min(y)));
    }
    let r = *dp.lookup(&amount).unwrap_or(&INF);
    Value::Int(if r >= INF { -1 } else { r })
}

// --- Word Break : dp[i] = Reduction(OR){dp[j] & s[j..i] in dict} ---
fn word_break(input: Value) -> Value {
    let parts = input.as_list();
    let s: Vec<char> = parts[0].as_str().chars().collect();
    let mut dict: ResourceRegistry<String, ()> = ResourceRegistry::new();
    for w in parts[1].as_list() {
        dict.insert(w.as_str().to_string(), ());
    }
    let n = s.len();
    let mut dp: ResourceRegistry<usize, bool> = ResourceRegistry::new();
    dp.insert(0, true);
    for i in 1..=n {
        let cands: Vec<bool> = (0..i)
            .map(|j| {
                let prefix_ok = *dp.lookup(&j).unwrap_or(&false);
                let word: String = s[j..i].iter().collect();
                prefix_ok && dict.contains(&word)
            })
            .collect();
        dp.insert(i, Reduction::reduce(cands, false, |a, b| a || b));
    }
    Value::Bool(*dp.lookup(&n).unwrap_or(&false))
}

// --- Unique Paths : dp[i][j] = Reduction(+){up, left} ---
fn unique_paths(input: Value) -> Value {
    let p = input.as_list();
    let m = p[0].as_int().max(1) as usize;
    let n = p[1].as_int().max(1) as usize;
    let mut dp: ResourceRegistry<(usize, usize), i64> = ResourceRegistry::new();
    for i in 0..m {
        for j in 0..n {
            let v = if i == 0 || j == 0 {
                1
            } else {
                Reduction::reduce(
                    vec![
                        *dp.lookup(&(i - 1, j)).unwrap(),
                        *dp.lookup(&(i, j - 1)).unwrap(),
                    ],
                    0,
                    |a, b| a + b,
                )
            };
            dp.insert((i, j), v);
        }
    }
    Value::Int(*dp.lookup(&(m - 1, n - 1)).unwrap())
}

// --- Longest Common Subsequence ---
fn lcs(input: Value) -> Value {
    let p = input.as_list();
    let a: Vec<char> = p[0].as_str().chars().collect();
    let b: Vec<char> = p[1].as_str().chars().collect();
    let mut dp: ResourceRegistry<(usize, usize), i64> = ResourceRegistry::new();
    for i in 0..=a.len() {
        for j in 0..=b.len() {
            let v = if i == 0 || j == 0 {
                0
            } else if a[i - 1] == b[j - 1] {
                *dp.lookup(&(i - 1, j - 1)).unwrap() + 1
            } else {
                Reduction::reduce(
                    vec![
                        *dp.lookup(&(i - 1, j)).unwrap(),
                        *dp.lookup(&(i, j - 1)).unwrap(),
                    ],
                    0,
                    |x, y| x.max(y),
                )
            };
            dp.insert((i, j), v);
        }
    }
    Value::Int(*dp.lookup(&(a.len(), b.len())).unwrap())
}

// --- Edit Distance ---
fn edit_distance(input: Value) -> Value {
    let p = input.as_list();
    let a: Vec<char> = p[0].as_str().chars().collect();
    let b: Vec<char> = p[1].as_str().chars().collect();
    let mut dp: ResourceRegistry<(usize, usize), i64> = ResourceRegistry::new();
    for i in 0..=a.len() {
        for j in 0..=b.len() {
            let v = if i == 0 {
                j as i64
            } else if j == 0 {
                i as i64
            } else if a[i - 1] == b[j - 1] {
                *dp.lookup(&(i - 1, j - 1)).unwrap()
            } else {
                1 + Reduction::reduce(
                    vec![
                        *dp.lookup(&(i - 1, j)).unwrap(),
                        *dp.lookup(&(i, j - 1)).unwrap(),
                        *dp.lookup(&(i - 1, j - 1)).unwrap(),
                    ],
                    INF,
                    |x, y| x.min(y),
                )
            };
            dp.insert((i, j), v);
        }
    }
    Value::Int(*dp.lookup(&(a.len(), b.len())).unwrap())
}

// --- 0/1 Knapsack ---
fn knapsack_01(input: Value) -> Value {
    let p = input.as_list();
    let w = p[0].as_int_vec();
    let val = p[1].as_int_vec();
    let cap = p[2].as_int().max(0) as usize;
    let n = w.len();
    let mut dp: ResourceRegistry<(usize, usize), i64> = ResourceRegistry::new();
    for c in 0..=cap {
        dp.insert((0, c), 0);
    }
    for i in 1..=n {
        for c in 0..=cap {
            let skip = *dp.lookup(&(i - 1, c)).unwrap();
            let wi = w[i - 1] as usize;
            let take = if wi <= c {
                *dp.lookup(&(i - 1, c - wi)).unwrap() + val[i - 1]
            } else {
                i64::MIN
            };
            dp.insert(
                (i, c),
                Reduction::reduce(vec![skip, take], i64::MIN, |x, y| x.max(y)),
            );
        }
    }
    Value::Int(*dp.lookup(&(n, cap)).unwrap())
}

// --- Longest Palindromic Subsequence (fill by length) ---
fn lps(input: Value) -> Value {
    let s: Vec<char> = input.as_str().chars().collect();
    let n = s.len();
    if n == 0 {
        return Value::Int(0);
    }
    let mut dp: ResourceRegistry<(usize, usize), i64> = ResourceRegistry::new();
    for i in 0..n {
        dp.insert((i, i), 1);
    }
    for len in 2..=n {
        for i in 0..=n - len {
            let j = i + len - 1;
            let v = if s[i] == s[j] {
                2 + if len == 2 {
                    0
                } else {
                    *dp.lookup(&(i + 1, j - 1)).unwrap()
                }
            } else {
                Reduction::reduce(
                    vec![
                        *dp.lookup(&(i + 1, j)).unwrap(),
                        *dp.lookup(&(i, j - 1)).unwrap(),
                    ],
                    0,
                    |x, y| x.max(y),
                )
            };
            dp.insert((i, j), v);
        }
    }
    Value::Int(*dp.lookup(&(0, n - 1)).unwrap())
}

// ---------- input generators (curated + property) ----------
fn g_climb() -> Vec<Value> {
    let mut v = vec![0, 1, 2, 3, 5, 10, 25, 35]
        .into_iter()
        .map(Value::Int)
        .collect::<Vec<_>>();
    v.extend(gen::rand_ints(11, 1000, 35));
    v
}
fn g_house() -> Vec<Value> {
    let mut v = vec![
        Value::ints(&[]),
        Value::ints(&[5]),
        Value::ints(&[2, 7, 9, 3, 1]),
        Value::ints(&[2, 1, 1, 2]),
    ];
    v.extend(gen::rand_int_lists(12, 1000, 12, 0, 30));
    v
}
fn g_lis() -> Vec<Value> {
    let mut v = vec![
        Value::ints(&[]),
        Value::ints(&[10, 9, 2, 5, 3, 7, 101, 18]),
        Value::ints(&[7, 7, 7]),
    ];
    v.extend(gen::rand_int_lists(13, 1000, 12, 0, 20));
    v
}
fn g_coin() -> Vec<Value> {
    let mut v = vec![
        Value::List(vec![Value::ints(&[1, 2, 5]), Value::Int(11)]),
        Value::List(vec![Value::ints(&[2]), Value::Int(3)]),
        Value::List(vec![Value::ints(&[1]), Value::Int(0)]),
    ];
    for i in 0..1000 {
        let coins = match i % 4 {
            0 => vec![1, 2, 5],
            1 => vec![2, 3, 7],
            2 => vec![1, 5, 10, 25],
            _ => vec![3, 4],
        };
        v.push(Value::List(vec![
            Value::ints(&coins),
            Value::Int((i % 40) as i64),
        ]));
    }
    v
}
fn g_wordbreak() -> Vec<Value> {
    let dict = |ws: &[&str]| Value::List(ws.iter().map(|w| Value::Str(w.to_string())).collect());
    let mut v = vec![
        Value::List(vec![Value::Str("leetcode".into()), dict(&["leet", "code"])]),
        Value::List(vec![
            Value::Str("applepenapple".into()),
            dict(&["apple", "pen"]),
        ]),
        Value::List(vec![
            Value::Str("catsandog".into()),
            dict(&["cats", "dog", "sand", "and", "cat"]),
        ]),
    ];
    let strs = gen::rand_strings(14, 1000, 8, 3);
    for s in strs {
        v.push(Value::List(vec![
            s,
            dict(&["a", "b", "c", "ab", "bc", "abc", "ca"]),
        ]));
    }
    v
}
fn g_unique() -> Vec<Value> {
    let mut v = vec![
        Value::List(vec![Value::Int(3), Value::Int(7)]),
        Value::List(vec![Value::Int(1), Value::Int(1)]),
        Value::List(vec![Value::Int(3), Value::Int(2)]),
    ];
    for i in 0..1000 {
        v.push(Value::List(vec![
            Value::Int(1 + (i % 8) as i64),
            Value::Int(1 + ((i / 8) % 8) as i64),
        ]));
    }
    v
}
fn g_two_str(seed: u64) -> Vec<Value> {
    let a = gen::rand_strings(seed, 1000, 7, 3);
    let b = gen::rand_strings(seed + 1, 1000, 7, 3);
    let mut v = vec![
        Value::List(vec![Value::Str("abcde".into()), Value::Str("ace".into())]),
        Value::List(vec![Value::Str("".into()), Value::Str("abc".into())]),
        Value::List(vec![Value::Str("horse".into()), Value::Str("ros".into())]),
    ];
    v.extend(a.into_iter().zip(b).map(|(x, y)| Value::List(vec![x, y])));
    v
}
fn g_lcs() -> Vec<Value> {
    g_two_str(20)
}
fn g_edit() -> Vec<Value> {
    g_two_str(30)
}
fn g_knap() -> Vec<Value> {
    let mut v = vec![Value::List(vec![
        Value::ints(&[1, 3, 4, 5]),
        Value::ints(&[1, 4, 5, 7]),
        Value::Int(7),
    ])];
    for i in 0..1000 {
        let w = vec![1 + (i % 5) as i64, 2 + (i % 4) as i64, 3 + (i % 3) as i64];
        let val = vec![(i % 7) as i64, 1 + (i % 6) as i64, 2 + (i % 5) as i64];
        v.push(Value::List(vec![
            Value::ints(&w),
            Value::ints(&val),
            Value::Int((i % 12) as i64),
        ]));
    }
    v
}
fn g_lps() -> Vec<Value> {
    let mut v = vec![
        Value::Str("bbbab".into()),
        Value::Str("cbbd".into()),
        Value::Str("".into()),
        Value::Str("a".into()),
    ];
    v.extend(gen::rand_strings(40, 1000, 9, 3));
    v
}

pub fn add(r: &mut Vec<CorpusEntry>) {
    let mz = "Memoization = ResourceRegistry + TraversalEngine(topo) + Reduction";
    entry(
        r,
        "Climbing Stairs",
        "1-D DP",
        1,
        "DAG",
        mz,
        climbing_stairs,
        "climbing_stairs",
        Equiv::Exact,
        g_climb,
    );
    entry(
        r,
        "House Robber",
        "1-D DP",
        1,
        "DAG",
        mz,
        house_robber,
        "house_robber",
        Equiv::Exact,
        g_house,
    );
    entry(
        r,
        "Longest Increasing Subsequence",
        "1-D DP",
        1,
        "DAG",
        mz,
        lis,
        "lis",
        Equiv::Exact,
        g_lis,
    );
    entry(
        r,
        "Coin Change",
        "1-D DP",
        1,
        "DAG",
        mz,
        coin_change,
        "coin_change",
        Equiv::Exact,
        g_coin,
    );
    entry(
        r,
        "Word Break",
        "1-D DP",
        1,
        "DAG",
        mz,
        word_break,
        "word_break",
        Equiv::BoolEq,
        g_wordbreak,
    );
    entry(
        r,
        "Unique Paths",
        "2-D DP",
        1,
        "DAG",
        mz,
        unique_paths,
        "unique_paths",
        Equiv::Exact,
        g_unique,
    );
    entry(
        r,
        "Longest Common Subsequence",
        "2-D DP",
        1,
        "DAG",
        mz,
        lcs,
        "lcs",
        Equiv::Exact,
        g_lcs,
    );
    entry(
        r,
        "Edit Distance",
        "2-D DP",
        1,
        "DAG",
        mz,
        edit_distance,
        "edit_distance",
        Equiv::Exact,
        g_edit,
    );
    entry(
        r,
        "0/1 Knapsack",
        "2-D DP",
        1,
        "DAG",
        mz,
        knapsack_01,
        "knapsack_01",
        Equiv::Exact,
        g_knap,
    );
    entry(
        r,
        "Longest Palindromic Subsequence",
        "2-D DP",
        1,
        "DAG",
        mz,
        lps,
        "lps",
        Equiv::Exact,
        g_lps,
    );
}
