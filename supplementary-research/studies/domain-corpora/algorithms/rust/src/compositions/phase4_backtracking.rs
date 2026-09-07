//! Phase 4 — Backtracking.
//!
//! Every algorithm here is the **Backtracking composition**: a
//! `TraversalEngine::backtrack` (paired-undo driver) over an implicit
//! decision tree.  Word Search and N-Queens additionally use
//! `ResourceRegistry` for visited / occupied sets.
//!
//! Structural ordering: **Tree** (the 2^N / N! / etc. decision tree).
//! Every case uses `TraversalEngine::backtrack`; none introduces a
//! separate recursion mechanism.
//!
//! ## I/O encoding (Rust ↔ Python identical)
//!
//! | Algorithm       | Input                               | Output                        | Equiv           |
//! |-----------------|-------------------------------------|-------------------------------|-----------------|
//! | Subsets         | `Value::ints(nums)`                 | `Value::List` of `Value::ints`| `SetOfIntLists` |
//! | Combination Sum | `[Value::ints(cands), Value::Int t]`| `Value::List` of `Value::ints`| `SetOfIntLists` |
//! | Permutations    | `Value::ints(nums)`                 | `Value::List` of `Value::ints`| `SetOfIntLists` |
//! | Word Search     | `[List[Str] rows, Str word]`        | `Value::Bool`                 | `BoolEq`        |
//! | N-Queens        | `Value::Int n`                      | `Value::Int count`            | `Exact`         |

use super::entry;
use crate::config::CorpusEntry;
use crate::equivalence::Equiv;
use crate::primitives::{ResourceRegistry, TraversalEngine};
use crate::value::Value;

// ===================================================================
// Subsets
// ===================================================================
//
// Decision tree of depth N; each node either includes or skips the
// element at the current index.  State: (current_index, current_subset).
// Every node is a solution (the subset so far), so `accept` always fires.
// `extend` yields moves only when there is a next element to decide on.
// The move is an Option<i64>: Some(v) = include element v, None = skip.
//
// TraversalEngine::backtrack is the sole traversal primitive.

#[derive(Clone)]
struct SubsetsState {
    nums: Vec<i64>,
    idx: usize,
    current: Vec<i64>,
}

fn subsets(input: Value) -> Value {
    let nums = input.as_int_vec();
    let mut state = SubsetsState {
        nums,
        idx: 0,
        current: Vec::new(),
    };
    let mut out: Vec<Value> = Vec::new();

    // Each move is a bool: true = include nums[idx], false = skip.
    TraversalEngine::backtrack(
        &mut state,
        // extend: if idx < len produce two moves (include, skip)
        &|st| {
            if st.idx < st.nums.len() {
                vec![true, false]
            } else {
                vec![]
            }
        },
        // apply
        &|st, &include| {
            if include {
                st.current.push(st.nums[st.idx]);
            }
            st.idx += 1;
        },
        // undo
        &|st, &include| {
            st.idx -= 1;
            if include {
                st.current.pop();
            }
        },
        // accept: emit at every node (not just leaves) — this enumerates
        // all 2^N subsets by collecting on every call.
        // To avoid duplicates, accept only when idx == len (leaf).
        &|st| {
            if st.idx == st.nums.len() {
                Some(Value::ints(&st.current))
            } else {
                None
            }
        },
        &mut out,
    );
    Value::List(out)
}

// ===================================================================
// Combination Sum
// ===================================================================
//
// Candidates may be reused.  State: (start_index, remaining, current).
// `extend` yields moves (candidate_index, saved_start) for indices >= start
// where cands[i] <= rem.  Saving start in the move enables exact undo.
// `apply`: push cands[i], subtract from rem, set start = i (reuse).
// `undo`:  pop, add back, restore start from saved value in move.
// `accept`: emit when rem == 0.
//
// TraversalEngine::backtrack is the sole traversal primitive.
// Note: the move encodes (i, prior_start) so undo can restore start
// exactly without hand-rolling recursion outside backtrack.

fn combination_sum_inner(cands: &[i64], target: i64) -> Vec<Value> {
    // Move = (candidate_index, prior_start)
    #[derive(Clone)]
    struct CS {
        cands: Vec<i64>,
        start: usize,
        rem: i64,
        current: Vec<i64>,
    }

    let mut state = CS {
        cands: cands.to_vec(),
        start: 0,
        rem: target,
        current: Vec::new(),
    };
    let mut out: Vec<Value> = Vec::new();

    TraversalEngine::backtrack(
        &mut state,
        &|st| {
            // Move = (candidate_index, saved_start)
            (st.start..st.cands.len())
                .filter(|&i| st.cands[i] <= st.rem)
                .map(|i| (i, st.start))
                .collect::<Vec<_>>()
        },
        &|st, &(i, _prior)| {
            let v = st.cands[i];
            st.current.push(v);
            st.rem -= v;
            st.start = i; // allow reuse of same candidate
        },
        &|st, &(_i, prior)| {
            let v = st.current.pop().unwrap();
            st.rem += v;
            st.start = prior; // restore exact prior start
        },
        &|st| {
            if st.rem == 0 {
                Some(Value::ints(&st.current))
            } else {
                None
            }
        },
        &mut out,
    );
    out
}

fn combination_sum_fn(input: Value) -> Value {
    let parts = input.as_list();
    let cands = parts[0].as_int_vec();
    let target = parts[1].as_int();
    Value::List(combination_sum_inner(&cands, target))
}

// ===================================================================
// Permutations
// ===================================================================
//
// State: (current_permutation, used ResourceRegistry<usize, ()>).
// `extend` yields indices not yet used.
// `apply`: push nums[i], mark i used.
// `undo`: pop, unmark i.
// `accept`: emit when len(current) == len(nums).

#[derive(Clone)]
struct PermState {
    nums: Vec<i64>,
    current: Vec<i64>,
    used: ResourceRegistry<usize, ()>,
}

fn permutations(input: Value) -> Value {
    let nums = input.as_int_vec();
    let n = nums.len();
    let mut state = PermState {
        nums,
        current: Vec::new(),
        used: ResourceRegistry::new(),
    };
    let mut out: Vec<Value> = Vec::new();

    TraversalEngine::backtrack(
        &mut state,
        &|st| {
            (0..st.nums.len())
                .filter(|i| !st.used.contains(i))
                .collect::<Vec<_>>()
        },
        &|st, &i| {
            st.current.push(st.nums[i]);
            st.used.insert(i, ());
        },
        &|st, &i| {
            st.current.pop();
            st.used.delete(&i);
        },
        &|st| {
            if st.current.len() == n {
                Some(Value::ints(&st.current))
            } else {
                None
            }
        },
        &mut out,
    );
    Value::List(out)
}

// ===================================================================
// Word Search
// ===================================================================
//
// For each starting cell (r, c) that matches word[0], run
// TraversalEngine::backtrack over the 4-connected grid.
//
// State: (grid_chars, word_chars, depth, visited ResourceRegistry<(usize,usize), ()>).
// Move = (r, c) of the next cell to visit.
// `extend`: 4-neighbors of current head where grid[r][c] == word[depth]
//            and (r,c) not in visited.
// `apply`: mark (r,c) visited, advance depth.
// `undo`: unmark (r,c), regress depth.
// `accept`: emit when depth == word.len() (full match found; use
//           Option<bool> sentinel to short-circuit via the out vec).
//
// Word Search and N-Queens additionally use ResourceRegistry.

#[derive(Clone)]
struct WSState {
    grid: Vec<Vec<char>>,
    word: Vec<char>,
    path: Vec<(usize, usize)>, // current path (last = current head)
    visited: ResourceRegistry<(usize, usize), ()>,
}

fn word_search(input: Value) -> Value {
    let parts = input.as_list();
    let rows: Vec<Vec<char>> = parts[0]
        .as_list()
        .iter()
        .map(|v| v.as_str().chars().collect())
        .collect();
    let word: Vec<char> = parts[1].as_str().chars().collect();

    if word.is_empty() {
        return Value::Bool(true);
    }
    if rows.is_empty() || rows[0].is_empty() {
        return Value::Bool(false);
    }

    let nrows = rows.len();
    let ncols = rows[0].len();

    // Try each starting cell that matches word[0]
    for sr in 0..nrows {
        for sc in 0..ncols {
            if rows[sr][sc] != word[0] {
                continue;
            }

            let mut visited: ResourceRegistry<(usize, usize), ()> = ResourceRegistry::new();
            visited.insert((sr, sc), ());

            let mut state = WSState {
                grid: rows.clone(),
                word: word.clone(),
                path: vec![(sr, sc)],
                visited,
            };
            let mut found: Vec<bool> = Vec::new();

            // If word is length 1, found immediately
            if word.len() == 1 {
                return Value::Bool(true);
            }

            TraversalEngine::backtrack(
                &mut state,
                &|st| {
                    let depth = st.path.len(); // next char to match is word[depth]
                    if depth >= st.word.len() {
                        return vec![];
                    }
                    let (r, c) = *st.path.last().unwrap();
                    let nrows = st.grid.len();
                    let ncols = st.grid[0].len();
                    let target = st.word[depth];
                    let mut moves = Vec::new();
                    for (dr, dc) in [(!0usize, 0usize), (1, 0), (0, !0), (0, 1)] {
                        let nr = r.wrapping_add(dr);
                        let nc = c.wrapping_add(dc);
                        if nr < nrows
                            && nc < ncols
                            && st.grid[nr][nc] == target
                            && !st.visited.contains(&(nr, nc))
                        {
                            moves.push((nr, nc));
                        }
                    }
                    moves
                },
                &|st, &(nr, nc)| {
                    st.path.push((nr, nc));
                    st.visited.insert((nr, nc), ());
                },
                &|st, &(nr, nc)| {
                    st.path.pop();
                    st.visited.delete(&(nr, nc));
                },
                &|st| {
                    if st.path.len() == st.word.len() {
                        Some(true)
                    } else {
                        None
                    }
                },
                &mut found,
            );

            if !found.is_empty() {
                return Value::Bool(true);
            }
        }
    }

    Value::Bool(false)
}

// ===================================================================
// N-Queens
// ===================================================================
//
// Place queens row by row (depth = current row).
// State: (n, depth, col_reg, diag_reg, anti_reg).
// Move = column c for row `depth`.
// `extend`: columns in 0..n not in col_reg, diag (depth-c), anti (depth+c).
// `apply`: insert c, depth-c, depth+c into the three registries; depth++.
// `undo`: delete; depth--.
// `accept`: emit count+1 when depth == n.
//
// Three ResourceRegistry instances for occupied columns, diagonals and
// anti-diagonals.

#[derive(Clone)]
struct NQState {
    n: usize,
    depth: usize,
    cols: ResourceRegistry<i64, ()>,
    diags: ResourceRegistry<i64, ()>,
    antis: ResourceRegistry<i64, ()>,
}

fn n_queens(input: Value) -> Value {
    let n = input.as_int().max(0) as usize;
    let mut state = NQState {
        n,
        depth: 0,
        cols: ResourceRegistry::new(),
        diags: ResourceRegistry::new(),
        antis: ResourceRegistry::new(),
    };
    let mut out: Vec<()> = Vec::new();

    TraversalEngine::backtrack(
        &mut state,
        &|st| {
            if st.depth >= st.n {
                return vec![];
            }
            let row = st.depth as i64;
            (0..st.n as i64)
                .filter(|&c| {
                    !st.cols.contains(&c)
                        && !st.diags.contains(&(row - c))
                        && !st.antis.contains(&(row + c))
                })
                .collect::<Vec<i64>>()
        },
        &|st, &c| {
            let row = st.depth as i64;
            st.cols.insert(c, ());
            st.diags.insert(row - c, ());
            st.antis.insert(row + c, ());
            st.depth += 1;
        },
        &|st, &c| {
            st.depth -= 1;
            let row = st.depth as i64;
            st.cols.delete(&c);
            st.diags.delete(&(row - c));
            st.antis.delete(&(row + c));
        },
        &|st| {
            if st.depth == st.n {
                Some(())
            } else {
                None
            }
        },
        &mut out,
    );

    Value::Int(out.len() as i64)
}

// ===================================================================
// Input generators
// ===================================================================

fn g_subsets() -> Vec<Value> {
    let mut v = vec![
        Value::ints(&[]),
        Value::ints(&[1]),
        Value::ints(&[1, 2]),
        Value::ints(&[1, 2, 3]),
        Value::ints(&[0, -1, 2]),
    ];
    // Property inputs: distinct ints, n in 1..=7
    let mut s = crate::primitives::Sampler::new(41);
    for _ in 0..60 {
        let n = 1 + s.pick_index(7); // 1..=7
        let mut seen = std::collections::HashSet::new();
        let mut nums = Vec::new();
        while nums.len() < n {
            let x = s.pick_index(20) as i64 - 10; // -10..=9
            if seen.insert(x) {
                nums.push(x);
            }
        }
        v.push(Value::ints(&nums));
    }
    v
}

fn g_comb_sum() -> Vec<Value> {
    let mut v = vec![
        Value::List(vec![Value::ints(&[2, 3, 6, 7]), Value::Int(7)]),
        Value::List(vec![Value::ints(&[2, 3, 5]), Value::Int(8)]),
        Value::List(vec![Value::ints(&[2]), Value::Int(1)]),
        Value::List(vec![Value::ints(&[1]), Value::Int(0)]),
        Value::List(vec![Value::ints(&[3, 5, 7]), Value::Int(15)]),
    ];
    // Property: small candidate sets, target <= 25
    let mut s = crate::primitives::Sampler::new(42);
    for _ in 0..80 {
        let nc = 2 + s.pick_index(4); // 2..=5
        let mut seen = std::collections::HashSet::new();
        let mut cands = Vec::new();
        while cands.len() < nc {
            let c = 1 + s.pick_index(8) as i64; // 1..=8
            if seen.insert(c) {
                cands.push(c);
            }
        }
        let target = 1 + s.pick_index(25) as i64; // 1..=25
        v.push(Value::List(vec![Value::ints(&cands), Value::Int(target)]));
    }
    v
}

fn g_perms() -> Vec<Value> {
    let mut v = vec![
        Value::ints(&[]),
        Value::ints(&[1]),
        Value::ints(&[1, 2]),
        Value::ints(&[1, 2, 3]),
        Value::ints(&[-1, 0, 1]),
    ];
    // Property: distinct ints, n in 1..=7
    let mut s = crate::primitives::Sampler::new(43);
    for _ in 0..60 {
        let n = 1 + s.pick_index(7); // 1..=7
        let mut seen = std::collections::HashSet::new();
        let mut nums = Vec::new();
        while nums.len() < n {
            let x = s.pick_index(20) as i64 - 10;
            if seen.insert(x) {
                nums.push(x);
            }
        }
        v.push(Value::ints(&nums));
    }
    v
}

fn g_word_search() -> Vec<Value> {
    // Curated cases
    let grid =
        |rows: &[&str]| Value::List(rows.iter().map(|r| Value::Str(r.to_string())).collect());
    let mut v = vec![
        // classic 3x4
        Value::List(vec![
            grid(&["ABCE", "SFCS", "ADEE"]),
            Value::Str("ABCCED".into()),
        ]),
        Value::List(vec![
            grid(&["ABCE", "SFCS", "ADEE"]),
            Value::Str("SEE".into()),
        ]),
        Value::List(vec![
            grid(&["ABCE", "SFCS", "ADEE"]),
            Value::Str("ABCB".into()),
        ]),
        // single cell
        Value::List(vec![grid(&["A"]), Value::Str("A".into())]),
        Value::List(vec![grid(&["A"]), Value::Str("B".into())]),
        // empty word
        Value::List(vec![grid(&["AB"]), Value::Str("".into())]),
    ];

    // Property: random 3x3 and 4x4 grids over {A,B,C,D}, words of len 1..=4
    let mut s = crate::primitives::Sampler::new(44);
    let alpha = ['A', 'B', 'C', 'D'];
    for _ in 0..80 {
        let rows = 2 + s.pick_index(3); // 2..=4
        let cols = 2 + s.pick_index(3);
        let grid_rows: Vec<String> = (0..rows)
            .map(|_| (0..cols).map(|_| alpha[s.pick_index(4)]).collect())
            .collect();
        let wlen = 1 + s.pick_index(4); // 1..=4
        let word: String = (0..wlen).map(|_| alpha[s.pick_index(4)]).collect();
        v.push(Value::List(vec![
            Value::List(grid_rows.iter().map(|r| Value::Str(r.clone())).collect()),
            Value::Str(word),
        ]));
    }
    v
}

fn g_nqueens() -> Vec<Value> {
    // Curated: n=0..=8
    let mut v: Vec<Value> = (0i64..=8).map(Value::Int).collect();
    // Property: repeat small values with varied ordering
    let mut s = crate::primitives::Sampler::new(45);
    for _ in 0..50 {
        let n = s.pick_index(9) as i64; // 0..=8
        v.push(Value::Int(n));
    }
    v
}

// ===================================================================
// Registration
// ===================================================================

pub fn add(r: &mut Vec<CorpusEntry>) {
    let bt = "TraversalEngine::backtrack (paired-undo driver)";
    let bt_reg = "TraversalEngine::backtrack + ResourceRegistry (visited/occupied)";

    entry(
        r,
        "Subsets",
        "Backtracking",
        4,
        "Tree",
        bt,
        subsets,
        "subsets",
        Equiv::SetOfIntLists,
        g_subsets,
    );
    entry(
        r,
        "Combination Sum",
        "Backtracking",
        4,
        "Tree",
        bt,
        combination_sum_fn,
        "combination_sum",
        Equiv::SetOfIntLists,
        g_comb_sum,
    );
    entry(
        r,
        "Permutations",
        "Backtracking",
        4,
        "Tree",
        bt_reg,
        permutations,
        "permutations",
        Equiv::SetOfIntLists,
        g_perms,
    );
    entry(
        r,
        "Word Search",
        "Backtracking",
        4,
        "Tree",
        bt_reg,
        word_search,
        "word_search",
        Equiv::BoolEq,
        g_word_search,
    );
    entry(
        r,
        "N-Queens",
        "Backtracking",
        4,
        "Tree",
        bt_reg,
        n_queens,
        "n_queens",
        Equiv::Exact,
        g_nqueens,
    );
}
