// phase6 arrays KAT.
extern crate algorithms_verus;
use algorithms_verus::instantiations::phase6_arrays::{
    buy_sell_stock, container_with_most_water, contains_duplicate, group_anagrams_count,
    longest_consecutive, longest_no_repeat, longest_repeating_char_replacement,
    min_window_substring, product_except_self, sliding_window_maximum, three_sum_count,
    top_k_frequent_count, trapping_rain_water, two_sum, two_sum_ii, valid_palindrome,
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
    println!("phase6 arrays KAT (Verus build)");
    let mut all_ok = true;

    all_ok &= check(
        "contains_duplicate([1,2,3,1])",
        contains_duplicate(&[1i64, 2, 3, 1]),
        true,
    );
    all_ok &= check(
        "contains_duplicate([1,2,3,4])",
        contains_duplicate(&[1i64, 2, 3, 4]),
        false,
    );

    let (i, j) = two_sum(&[2i64, 7, 11, 15], 9);
    all_ok &= check("two_sum [2,7,11,15],9 -> (0,1)", (i, j), (0, 1));

    let dict: Vec<Vec<u8>> = vec![
        b"eat".to_vec(),
        b"tea".to_vec(),
        b"tan".to_vec(),
        b"ate".to_vec(),
        b"nat".to_vec(),
        b"bat".to_vec(),
    ];
    all_ok &= check("group_anagrams_count = 3", group_anagrams_count(&dict), 3);

    all_ok &= check(
        "top_k_frequent_count([1,1,1,2,2,3],2) = 5",
        top_k_frequent_count(&[1i64, 1, 1, 2, 2, 3], 2),
        5,
    );

    let pe = product_except_self(&[1i64, 2, 3, 4]);
    all_ok &= check("product_except_self[0]=24", pe[0], 24);
    all_ok &= check("product_except_self[1]=12", pe[1], 12);
    all_ok &= check("product_except_self[3]=6", pe[3], 6);

    all_ok &= check(
        "longest_consecutive([100,4,200,1,3,2]) = 4",
        longest_consecutive(&[100i64, 4, 200, 1, 3, 2]),
        4,
    );

    all_ok &= check(
        "valid_palindrome (\"A man, a plan...\")",
        valid_palindrome(b"A man, a plan, a canal: Panama"),
        true,
    );
    all_ok &= check(
        "valid_palindrome (\"race a car\")",
        valid_palindrome(b"race a car"),
        false,
    );

    let (i2, j2) = two_sum_ii(&[2i64, 7, 11, 15], 9);
    all_ok &= check("two_sum_ii", (i2, j2), (0, 1));

    all_ok &= check(
        "three_sum_count([-1,0,1,2,-1,-4]) = 2",
        three_sum_count(&[-1i64, 0, 1, 2, -1, -4]),
        2,
    );

    all_ok &= check(
        "container_with_most_water",
        container_with_most_water(&[1u64, 8, 6, 2, 5, 4, 8, 3, 7]),
        49,
    );

    all_ok &= check(
        "trapping_rain_water",
        trapping_rain_water(&[0u64, 1, 0, 2, 1, 0, 1, 3, 2, 1, 2, 1]),
        6,
    );

    all_ok &= check(
        "buy_sell_stock([7,1,5,3,6,4]) = 5",
        buy_sell_stock(&[7u64, 1, 5, 3, 6, 4]),
        5,
    );
    all_ok &= check(
        "buy_sell_stock([7,6,4,3,1]) = 0",
        buy_sell_stock(&[7u64, 6, 4, 3, 1]),
        0,
    );

    all_ok &= check(
        "longest_no_repeat(\"abcabcbb\") = 3",
        longest_no_repeat(b"abcabcbb"),
        3,
    );
    all_ok &= check(
        "longest_no_repeat(\"bbbbb\") = 1",
        longest_no_repeat(b"bbbbb"),
        1,
    );

    all_ok &= check(
        "longest_repeating_char_replacement(\"ABAB\", 2) = 4",
        longest_repeating_char_replacement(b"ABAB", 2),
        4,
    );

    all_ok &= check(
        "min_window_substring(\"ADOBECODEBANC\", \"ABC\") = 4",
        min_window_substring(b"ADOBECODEBANC", b"ABC"),
        4,
    );

    let swm = sliding_window_maximum(&[1i64, 3, -1, -3, 5, 3, 6, 7], 3);
    all_ok &= check("sliding_window_maximum.len", swm.len(), 6);
    all_ok &= check("sliding_window_maximum[0] = 3", swm[0], 3);
    all_ok &= check("sliding_window_maximum[5] = 7", swm[5], 7);

    if all_ok {
        println!("KAT_RESULT: SUCCESS (phase6 16/16)");
        std::process::exit(0);
    } else {
        println!("KAT_RESULT: FAIL");
        std::process::exit(1);
    }
}
