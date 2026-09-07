// phase1_dp known-answer tests. Ten DP algorithms exercised against
// hand-picked inputs whose mathematical outputs are computed by
// inspection. The executable Rust oracle in supplementary-research/studies/domain-corpora/algorithms/rust/src/
// compositions/phase1_dp.rs runs these same inputs through its own
// implementation and the corpus-comparison harness validates the
// match.
extern crate algorithms_verus;
use algorithms_verus::instantiations::phase1_dp::{
    climbing_stairs, coin_change, edit_distance, house_robber, knapsack_01, lcs, lis, lps,
    unique_paths, word_break,
};

fn check<T: std::fmt::Debug + PartialEq>(name: &str, got: T, want: T) -> bool {
    if got == want {
        println!("  PASS  {}", name);
        true
    } else {
        println!("  FAIL  {}: got {:?}, want {:?}", name, got, want);
        false
    }
}

fn main() {
    println!("phase1 DP KAT cross-check (Verus build)");
    let mut all_ok = true;

    // climbing_stairs: 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89.
    all_ok &= check("climbing_stairs(0)", climbing_stairs(0), 1);
    all_ok &= check("climbing_stairs(1)", climbing_stairs(1), 1);
    all_ok &= check("climbing_stairs(2)", climbing_stairs(2), 2);
    all_ok &= check("climbing_stairs(10)", climbing_stairs(10), 89);
    all_ok &= check("climbing_stairs(25)", climbing_stairs(25), 121393);

    // house_robber: max non-adjacent sum.
    all_ok &= check("house_robber([])", house_robber(&[]), 0);
    all_ok &= check("house_robber([5])", house_robber(&[5u64]), 5);
    all_ok &= check(
        "house_robber([2,7,9,3,1]) = 12",
        house_robber(&[2u64, 7, 9, 3, 1]),
        12,
    );
    all_ok &= check(
        "house_robber([2,1,1,2]) = 4",
        house_robber(&[2u64, 1, 1, 2]),
        4,
    );

    // lis: longest increasing subsequence length.
    all_ok &= check("lis([])", lis(&[]), 0);
    all_ok &= check(
        "lis([10,9,2,5,3,7,101,18]) = 4",
        lis(&[10u64, 9, 2, 5, 3, 7, 101, 18]),
        4,
    );
    all_ok &= check("lis([7,7,7]) = 1", lis(&[7u64, 7, 7]), 1);
    all_ok &= check("lis([1,2,3,4,5]) = 5", lis(&[1u64, 2, 3, 4, 5]), 5);

    // coin_change: min coins to make amount, u64::MAX if unreachable.
    all_ok &= check(
        "coin_change([1,2,5], 11) = 3",
        coin_change(&[1u64, 2, 5], 11),
        3,
    );
    all_ok &= check(
        "coin_change([2], 3) = u64::MAX (unreachable)",
        coin_change(&[2u64], 3),
        u64::MAX,
    );
    all_ok &= check("coin_change([1], 0) = 0", coin_change(&[1u64], 0), 0);

    // word_break.
    let dict_a: Vec<Vec<u8>> = vec![b"leet".to_vec(), b"code".to_vec()];
    all_ok &= check(
        "word_break(\"leetcode\", [leet,code])",
        word_break(b"leetcode", &dict_a),
        true,
    );
    let dict_b: Vec<Vec<u8>> = vec![b"apple".to_vec(), b"pen".to_vec()];
    all_ok &= check(
        "word_break(\"applepenapple\", [apple,pen])",
        word_break(b"applepenapple", &dict_b),
        true,
    );
    let dict_c: Vec<Vec<u8>> = vec![
        b"cats".to_vec(),
        b"dog".to_vec(),
        b"sand".to_vec(),
        b"and".to_vec(),
        b"cat".to_vec(),
    ];
    all_ok &= check(
        "word_break(\"catsandog\", ...) = false",
        word_break(b"catsandog", &dict_c),
        false,
    );

    // unique_paths(m, n) = C(m+n-2, m-1).
    all_ok &= check("unique_paths(3,7) = 28", unique_paths(3, 7), 28);
    all_ok &= check("unique_paths(1,1) = 1", unique_paths(1, 1), 1);
    all_ok &= check("unique_paths(3,2) = 3", unique_paths(3, 2), 3);

    // lcs.
    all_ok &= check("lcs(abcde, ace) = 3", lcs(b"abcde", b"ace"), 3);
    all_ok &= check("lcs(\"\", abc) = 0", lcs(b"", b"abc"), 0);
    all_ok &= check("lcs(abc, def) = 0", lcs(b"abc", b"def"), 0);

    // edit_distance.
    all_ok &= check(
        "edit_distance(horse, ros) = 3",
        edit_distance(b"horse", b"ros"),
        3,
    );
    all_ok &= check(
        "edit_distance(\"\", abc) = 3",
        edit_distance(b"", b"abc"),
        3,
    );
    all_ok &= check(
        "edit_distance(same, same) = 0",
        edit_distance(b"same", b"same"),
        0,
    );

    // knapsack_01: max value within capacity.
    // weights=[1,3,4,5], values=[1,4,5,7], cap=7. Expected: pick weights {3,4}→values 4+5=9.
    all_ok &= check(
        "knapsack_01([1,3,4,5],[1,4,5,7],7) = 9",
        knapsack_01(&[1u64, 3, 4, 5], &[1u64, 4, 5, 7], 7),
        9,
    );
    all_ok &= check("knapsack_01([],[],10) = 0", knapsack_01(&[], &[], 10), 0);

    // lps.
    all_ok &= check("lps(\"bbbab\") = 4 (bbbb)", lps(b"bbbab"), 4);
    all_ok &= check("lps(\"cbbd\") = 2 (bb)", lps(b"cbbd"), 2);
    all_ok &= check("lps(\"\") = 0", lps(b""), 0);
    all_ok &= check("lps(\"a\") = 1", lps(b"a"), 1);

    if all_ok {
        println!("KAT_RESULT: SUCCESS (phase1 10/10 DP algorithms at )");
        std::process::exit(0);
    } else {
        println!("KAT_RESULT: FAIL");
        std::process::exit(1);
    }
}
