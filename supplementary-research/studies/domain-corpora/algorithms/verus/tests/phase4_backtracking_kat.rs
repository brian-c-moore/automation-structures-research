// phase4 backtracking KAT.
extern crate algorithms_verus;
use algorithms_verus::instantiations::phase4_backtracking::{
    combination_sum_count, n_queens_count, permutations_count, subsets_count, word_search,
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
    println!("phase4 backtracking KAT (Verus build)");
    let mut all_ok = true;

    all_ok &= check(
        "subsets_count([1,2,3]) = 8",
        subsets_count(&[1i64, 2, 3]),
        8,
    );
    all_ok &= check("subsets_count([]) = 1", subsets_count(&[]), 1);

    // combination_sum: [2,3,6,7], target=7. Combinations: [7], [2,2,3] → 2.
    all_ok &= check(
        "combination_sum_count([2,3,6,7], 7) = 2",
        combination_sum_count(&[2i64, 3, 6, 7], 7),
        2,
    );

    all_ok &= check(
        "permutations_count([1,2,3]) = 6",
        permutations_count(&[1i64, 2, 3]),
        6,
    );
    all_ok &= check("permutations_count([]) = 1", permutations_count(&[]), 1);

    // word_search: 3x4 grid.
    // A B C E
    // S F C S
    // A D E E
    let grid = b"ABCESFCSADEE";
    all_ok &= check(
        "word_search(ABCCED)",
        word_search(3, 4, grid, b"ABCCED"),
        true,
    );
    all_ok &= check("word_search(SEE)", word_search(3, 4, grid, b"SEE"), true);
    all_ok &= check(
        "word_search(ABCB) absent",
        word_search(3, 4, grid, b"ABCB"),
        false,
    );

    all_ok &= check("n_queens_count(4) = 2", n_queens_count(4), 2);
    all_ok &= check("n_queens_count(5) = 10", n_queens_count(5), 10);
    all_ok &= check("n_queens_count(8) = 92", n_queens_count(8), 92);

    if all_ok {
        println!("KAT_RESULT: SUCCESS (phase4 5/5)");
        std::process::exit(0);
    } else {
        println!("KAT_RESULT: FAIL");
        std::process::exit(1);
    }
}
