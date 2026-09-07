// phase8 greedy/intervals/math/bit KAT.
extern crate algorithms_verus;
use algorithms_verus::instantiations::phase8_greedy_intervals_math_bit::{
    counting_bits, gas_station, hamming_weight, hand_of_straights, happy_number, insert_interval,
    jump_game, maximum_subarray, meeting_rooms_ii, merge_intervals, missing_number,
    non_overlapping_intervals, pow_xn, reverse_bits, rotate_image, set_matrix_zeroes,
    single_number, spiral_matrix,
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
    println!("phase8 greedy/intervals/math/bit KAT (Verus build)");
    let mut all_ok = true;

    all_ok &= check(
        "maximum_subarray([-2,1,-3,4,-1,2,1,-5,4]) = 6",
        maximum_subarray(&[-2i64, 1, -3, 4, -1, 2, 1, -5, 4]),
        6,
    );

    all_ok &= check(
        "jump_game([2,3,1,1,4]) = true",
        jump_game(&[2u64, 3, 1, 1, 4]),
        true,
    );
    all_ok &= check(
        "jump_game([3,2,1,0,4]) = false",
        jump_game(&[3u64, 2, 1, 0, 4]),
        false,
    );

    all_ok &= check(
        "gas_station([1,2,3,4,5],[3,4,5,1,2]) = 3",
        gas_station(&[1i64, 2, 3, 4, 5], &[3i64, 4, 5, 1, 2]),
        3,
    );
    all_ok &= check(
        "gas_station([2,3,4],[3,4,3]) = -1",
        gas_station(&[2i64, 3, 4], &[3i64, 4, 3]),
        -1,
    );

    all_ok &= check(
        "hand_of_straights([1,2,3,6,2,3,4,7,8], 3) = true",
        hand_of_straights(&[1i64, 2, 3, 6, 2, 3, 4, 7, 8], 3),
        true,
    );
    all_ok &= check(
        "hand_of_straights([1,2,3,4,5], 4) = false",
        hand_of_straights(&[1i64, 2, 3, 4, 5], 4),
        false,
    );

    let (ms, me) = merge_intervals(&[1i64, 2, 8, 15], &[3i64, 6, 10, 18]);
    all_ok &= check("merge_intervals len = 3", ms.len(), 3);
    all_ok &= check("merge_intervals[0]=(1,6)", (ms[0], me[0]), (1, 6));

    let (is_, ie) = insert_interval(&[1i64, 3, 6, 9], &[2i64, 5, 7, 10], 4, 8);
    all_ok &= check("insert_interval result count = 3", is_.len(), 3);

    all_ok &= check(
        "non_overlapping_intervals([(1,2),(2,3),(3,4),(1,3)]) = 1",
        non_overlapping_intervals(&[1i64, 2, 3, 1], &[2i64, 3, 4, 3]),
        1,
    );

    all_ok &= check(
        "meeting_rooms_ii([(0,30),(5,10),(15,20)]) = 2",
        meeting_rooms_ii(&[0i64, 5, 15], &[30i64, 10, 20]),
        2,
    );

    let mat = [1i64, 2, 3, 4, 5, 6, 7, 8, 9];
    let rot = rotate_image(3, &mat);
    all_ok &= check("rotate_image[0] = 7", rot[0], 7);
    all_ok &= check("rotate_image[2] = 1", rot[2], 1);

    let mat2 = [1i64, 2, 3, 4, 5, 6, 7, 8, 9];
    let sp = spiral_matrix(3, 3, &mat2);
    all_ok &= check("spiral_matrix len", sp.len(), 9);
    all_ok &= check("spiral_matrix[0]=1", sp[0], 1);
    all_ok &= check("spiral_matrix[8]=5 (center last)", sp[8], 5);

    let mat3 = [1i64, 1, 1, 1, 0, 1, 1, 1, 1]; // 3x3 with one zero at (1,1)
    let smz = set_matrix_zeroes(3, 3, &mat3);
    all_ok &= check("set_matrix_zeroes row 1 zeroed", smz[1 * 3 + 0], 0);
    all_ok &= check("set_matrix_zeroes col 1 zeroed", smz[0 * 3 + 1], 0);
    all_ok &= check("set_matrix_zeroes preserved", smz[0 * 3 + 0], 1);

    all_ok &= check("pow_xn(2, 10) = 1024", pow_xn(2, 10), 1024);
    all_ok &= check("pow_xn(2, 0) = 1", pow_xn(2, 0), 1);
    all_ok &= check("pow_xn(3, 4) = 81", pow_xn(3, 4), 81);

    all_ok &= check("happy_number(19) = true", happy_number(19), true);
    all_ok &= check("happy_number(2) = false", happy_number(2), false);

    all_ok &= check("hamming_weight(11) = 3", hamming_weight(11), 3);
    all_ok &= check(
        "hamming_weight(0xFFFFFFFF) = 32",
        hamming_weight(0xFFFFFFFFu64),
        32,
    );

    all_ok &= check(
        "single_number([2,2,1]) = 1",
        single_number(&[2i64, 2, 1]),
        1,
    );
    all_ok &= check(
        "single_number([4,1,2,1,2]) = 4",
        single_number(&[4i64, 1, 2, 1, 2]),
        4,
    );

    all_ok &= check(
        "missing_number([3,0,1]) = 2",
        missing_number(&[3i64, 0, 1]),
        2,
    );
    all_ok &= check("missing_number([0,1]) = 2", missing_number(&[0i64, 1]), 2);

    let cb = counting_bits(5);
    all_ok &= check("counting_bits(5).len = 6", cb.len(), 6);
    all_ok &= check("counting_bits[5] = 2", cb[5], 2);
    all_ok &= check("counting_bits[3] = 2", cb[3], 2);

    all_ok &= check(
        "reverse_bits(0x00000001) = 0x80000000",
        reverse_bits(0x00000001),
        0x80000000,
    );
    all_ok &= check(
        "reverse_bits(0x80000000) = 0x00000001",
        reverse_bits(0x80000000),
        0x00000001,
    );

    if all_ok {
        println!("KAT_RESULT: SUCCESS (phase8 18/18)");
        std::process::exit(0);
    } else {
        println!("KAT_RESULT: FAIL");
        std::process::exit(1);
    }
}
