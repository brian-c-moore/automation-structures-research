// phase2 stack/bsearch KAT — cross-check.
extern crate algorithms_verus;
use algorithms_verus::instantiations::phase2_stack_bsearch::{
    binary_search, daily_temperatures, eval_rpn, find_min_rotated, koko_bananas,
    largest_rect_histogram, median_two_sorted, min_stack, search_rotated, valid_parentheses,
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
    println!("phase2 stack/bsearch KAT cross-check (Verus build)");
    let mut all_ok = true;

    all_ok &= check("valid_parentheses(\"()\")", valid_parentheses(b"()"), true);
    all_ok &= check(
        "valid_parentheses(\"()[]{}\")",
        valid_parentheses(b"()[]{}"),
        true,
    );
    all_ok &= check("valid_parentheses(\"(]\")", valid_parentheses(b"(]"), false);
    all_ok &= check("valid_parentheses(\"\")", valid_parentheses(b""), true);

    // min_stack: ops [push 3, push 5, getmin, pop, getmin] → [3, 3]
    let ops: Vec<u8> = vec![0, 0, 2, 1, 2];
    let vals: Vec<i64> = vec![3, 5, 0, 0, 0];
    let mins = min_stack(&ops, &vals);
    all_ok &= check("min_stack len", mins.len(), 2);
    all_ok &= check("min_stack[0]=3", mins[0], 3);
    all_ok &= check("min_stack[1]=3", mins[1], 3);

    // eval_rpn: "2 1 + 3 *" → (2+1)*3 = 9
    let op_add = i64::MIN;
    let op_mul = i64::MIN + 2;
    all_ok &= check(
        "eval_rpn(2 1 + 3 *)",
        eval_rpn(&[2, 1, op_add, 3, op_mul]),
        9,
    );

    // daily_temperatures([73,74,75,71,69,72,76,73]) → [1,1,4,2,1,1,0,0]
    let t = daily_temperatures(&[73i64, 74, 75, 71, 69, 72, 76, 73]);
    all_ok &= check("daily_temperatures[0]=1", t[0], 1u64);
    all_ok &= check("daily_temperatures[2]=4", t[2], 4u64);
    all_ok &= check("daily_temperatures[6]=0", t[6], 0u64);

    // largest_rect_histogram([2,1,5,6,2,3]) = 10
    all_ok &= check(
        "largest_rect([2,1,5,6,2,3])",
        largest_rect_histogram(&[2u64, 1, 5, 6, 2, 3]),
        10,
    );

    // binary_search.
    all_ok &= check(
        "binary_search([1,3,5,7,9], 5)",
        binary_search(&[1i64, 3, 5, 7, 9], 5),
        2,
    );
    all_ok &= check(
        "binary_search([1,3,5,7,9], 4) absent",
        binary_search(&[1i64, 3, 5, 7, 9], 4),
        -1,
    );

    // search_rotated([4,5,6,7,0,1,2], 0) = 4
    all_ok &= check(
        "search_rotated([4,5,6,7,0,1,2],0)",
        search_rotated(&[4i64, 5, 6, 7, 0, 1, 2], 0),
        4,
    );
    all_ok &= check(
        "search_rotated absent",
        search_rotated(&[4i64, 5, 6, 7, 0, 1, 2], 3),
        -1,
    );

    // find_min_rotated([3,4,5,1,2]) = 1
    all_ok &= check(
        "find_min_rotated([3,4,5,1,2])",
        find_min_rotated(&[3i64, 4, 5, 1, 2]),
        1,
    );

    // koko_bananas([3,6,7,11], h=8) = 4
    all_ok &= check(
        "koko_bananas([3,6,7,11], 8)",
        koko_bananas(&[3u64, 6, 7, 11], 8),
        4,
    );
    all_ok &= check(
        "koko_bananas([30,11,23,4,20], 6)",
        koko_bananas(&[30u64, 11, 23, 4, 20], 6),
        23,
    );

    // median_two_sorted: returns 2× median.
    // [1,3] [2] → median 2 → result 4.
    all_ok &= check(
        "median_two_sorted([1,3],[2])",
        median_two_sorted(&[1i64, 3], &[2i64]),
        4,
    );
    // [1,2] [3,4] → median 2.5 → result 5.
    all_ok &= check(
        "median_two_sorted([1,2],[3,4])",
        median_two_sorted(&[1i64, 2], &[3i64, 4]),
        5,
    );

    if all_ok {
        println!("KAT_RESULT: SUCCESS (phase2 10/10 algorithms at )");
        std::process::exit(0);
    } else {
        println!("KAT_RESULT: FAIL");
        std::process::exit(1);
    }
}
