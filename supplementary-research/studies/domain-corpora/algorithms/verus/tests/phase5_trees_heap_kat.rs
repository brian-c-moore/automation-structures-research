// phase5 trees/heap KAT.
extern crate algorithms_verus;
use algorithms_verus::instantiations::phase5_trees_heap::{
    find_median_stream, invert_binary_tree, k_closest_points, kth_largest_stream,
    last_stone_weight, level_order, max_depth, max_path_sum, same_tree, validate_bst, NULL_NODE,
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
    println!("phase5 trees/heap KAT (Verus build)");
    let mut all_ok = true;

    // Tree:    4
    //        /   \
    //       2     7
    //      / \   / \
    //     1   3 6   9
    let tree = [4i64, 2, 7, 1, 3, 6, 9];
    let inv = invert_binary_tree(&tree);
    all_ok &= check("invert root", inv[0], 4);
    all_ok &= check("invert level1[0] swapped", inv[1], 7);
    all_ok &= check("invert level1[1] swapped", inv[2], 2);

    all_ok &= check("max_depth(7-node tree) = 3", max_depth(&tree), 3);
    let leaf_only = [42i64];
    all_ok &= check("max_depth(leaf) = 1", max_depth(&leaf_only), 1);
    let empty: [i64; 0] = [];
    all_ok &= check("max_depth(empty) = 0", max_depth(&empty), 0);

    let t2 = [1i64, 2, 3];
    let t3 = [1i64, 2, 3];
    let t4 = [1i64, 2, 4];
    all_ok &= check("same_tree(t2,t3)", same_tree(&t2, &t3), true);
    all_ok &= check("same_tree(t2,t4)", same_tree(&t2, &t4), false);

    let lo = level_order(&tree);
    all_ok &= check("level_order.len", lo.len(), 7);
    all_ok &= check("level_order[0]", lo[0], 4);
    all_ok &= check("level_order[1]", lo[1], 2);

    let bst = [2i64, 1, 3];
    let not_bst = [5i64, 1, 4, NULL_NODE, NULL_NODE, 3, 6];
    all_ok &= check("validate_bst(bst)", validate_bst(&bst), true);
    all_ok &= check("validate_bst(not_bst)", validate_bst(&not_bst), false);

    all_ok &= check("max_path_sum(tree) = ?", max_path_sum(&tree) >= 4, true);

    all_ok &= check(
        "kth_largest_stream(3, [4,5,8,2,3,5,10,9,4]) = 8",
        kth_largest_stream(&[4i64, 5, 8, 2, 3, 5, 10, 9, 4], 3),
        8,
    );

    all_ok &= check(
        "last_stone_weight([2,7,4,1,8,1])",
        last_stone_weight(&[2u64, 7, 4, 1, 8, 1]),
        1,
    );

    let xs = [1i64, -2, 3, 5];
    let ys = [3i64, -2, 3, -1];
    let kcp = k_closest_points(&xs, &ys, 2);
    all_ok &= check("k_closest_points.len = 2", kcp.len(), 2);

    all_ok &= check(
        "find_median_stream([1,2,3]) (odd) = 2*2=4",
        find_median_stream(&[1i64, 2, 3]),
        4,
    );
    all_ok &= check(
        "find_median_stream([1,2,3,4]) (even) = 2+3=5",
        find_median_stream(&[1i64, 2, 3, 4]),
        5,
    );

    if all_ok {
        println!("KAT_RESULT: SUCCESS (phase5 10/10)");
        std::process::exit(0);
    } else {
        println!("KAT_RESULT: FAIL");
        std::process::exit(1);
    }
}
