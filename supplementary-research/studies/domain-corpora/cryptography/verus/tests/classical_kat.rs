// Classical composition-pattern known-answer tests. The six patterns
// (memoization, sort_then_scan, priority_driven_propagation,
// sliding_window, monotonic_stack, monotonic_deque) are exercised with
// hand-picked inputs whose mathematical outputs are computable by
// inspection.
extern crate cryptography_verus;
use cryptography_verus::compositions::classical::monotonic_deque::monotonic_push_back;
use cryptography_verus::compositions::classical::monotonic_stack::monotonic_push;
use cryptography_verus::compositions::classical::priority_driven_propagation::extract_min_index;
use cryptography_verus::compositions::classical::sliding_window::sliding_window_final_sum;
use cryptography_verus::compositions::classical::sort_then_scan::scan_sorted_count_adjacent_equal;
// The memoization module is imported to check that this crate exposes the
// composition. These tests do not claim a memoization refinement result.
#[allow(unused_imports)]
use cryptography_verus::compositions::classical::memoization as _v3a;

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
    println!("classical composition patterns KAT cross-check (Verus build)");
    let mut all_ok = true;

    // memoization: pattern linkage (DP KATs cover runtime).
    println!("  NOTE  memoization: via 1-D/2-D DP instantiations");

    // sort_then_scan: scan_sorted_count_adjacent_equal.
    // Sorted [1, 1, 2, 3, 3, 3] has adjacent-equal pairs at i=1, i=4, and i=5.
    all_ok &= check(
        "scan_sorted([1,1,2,3,3,3]) adjacent-equal count",
        scan_sorted_count_adjacent_equal(&[1u64, 1, 2, 3, 3, 3]),
        3,
    );
    all_ok &= check(
        "scan_sorted([]) count",
        scan_sorted_count_adjacent_equal(&[]),
        0,
    );
    all_ok &= check(
        "scan_sorted([5]) count",
        scan_sorted_count_adjacent_equal(&[5u64]),
        0,
    );
    all_ok &= check(
        "scan_sorted([1,2,3,4]) no dups",
        scan_sorted_count_adjacent_equal(&[1u64, 2, 3, 4]),
        0,
    );
    all_ok &= check(
        "scan_sorted([7,7,7,7,7]) all dups",
        scan_sorted_count_adjacent_equal(&[7u64, 7, 7, 7, 7]),
        4,
    );

    // priority_driven_propagation: extract_min_index.
    all_ok &= check(
        "extract_min_index([5,3,8,1,4])",
        extract_min_index(&[5u64, 3, 8, 1, 4]),
        3,
    );
    all_ok &= check("extract_min_index([42])", extract_min_index(&[42u64]), 0);
    all_ok &= check(
        "extract_min_index ties to first",
        extract_min_index(&[5u64, 3, 3, 5]),
        1,
    );

    // sliding_window_final_sum: sum of last `window_size` elements.
    all_ok &= check(
        "sliding_window_final_sum([1,2,3,4,5], 3) = 3+4+5",
        sliding_window_final_sum(&[1u64, 2, 3, 4, 5], 3),
        12,
    );
    all_ok &= check(
        "sliding_window_final_sum([10,20,30], 1) = 30",
        sliding_window_final_sum(&[10u64, 20, 30], 1),
        30,
    );
    all_ok &= check(
        "sliding_window_final_sum([1,2,3,4,5], 5) = 15 (all)",
        sliding_window_final_sum(&[1u64, 2, 3, 4, 5], 5),
        15,
    );

    // monotonic_stack: pop higher values, then push.
    let mut stack: Vec<u64> = Vec::new();
    monotonic_push(&mut stack, 5);
    monotonic_push(&mut stack, 10);
    monotonic_push(&mut stack, 7); // 10 > 7 so 10 pops; stack = [5, 7]
    all_ok &= check("monotonic_stack after pushes [5,10,7]: len", stack.len(), 2);
    all_ok &= check("monotonic_stack[0]", stack[0], 5);
    all_ok &= check("monotonic_stack[1]", stack[1], 7);
    monotonic_push(&mut stack, 3); // 7 > 3 so 7 pops; 5 > 3 so 5 pops; stack = [3]
    all_ok &= check("monotonic_stack after push 3: len", stack.len(), 1);
    all_ok &= check("monotonic_stack[0] after 3", stack[0], 3);

    // monotonic_deque: pop smaller back values, then push back.
    let mut dq: Vec<u64> = Vec::new();
    monotonic_push_back(&mut dq, 10);
    monotonic_push_back(&mut dq, 5); // 10 > 5: keep; deque = [10, 5]
    monotonic_push_back(&mut dq, 7); // 5 < 7: pop 5; deque = [10, 7]
    all_ok &= check("monotonic_deque after [10,5,7]: len", dq.len(), 2);
    all_ok &= check("monotonic_deque[0]", dq[0], 10);
    all_ok &= check("monotonic_deque[1]", dq[1], 7);
    monotonic_push_back(&mut dq, 12); // Pop 7, then 10; deque = [12]
    all_ok &= check("monotonic_deque after push 12: len", dq.len(), 1);
    all_ok &= check("monotonic_deque[0] after 12", dq[0], 12);

    if all_ok {
        println!("KAT_RESULT: SUCCESS (-3e at )");
        std::process::exit(0);
    } else {
        println!("KAT_RESULT: FAIL");
        std::process::exit(1);
    }
}
