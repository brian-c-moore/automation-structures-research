// Primitives known-answer tests, cross-checked against test vectors and
// the reference oracle. The six primitives (Reduction, ResourceRegistry,
// TraversalEngine, ActuationPass, Bisection, Sampler) are exercised on
// hand-picked inputs whose mathematical outputs are computable by
// inspection. The Verus-verified functions are called from this binary
// linked against the Verus-compiled library; any mismatch between the
// computed answer and the expected answer surfaces as a FAIL.
extern crate algorithms_verus;
use algorithms_verus::primitives::actuation_pass::{actuate_pass_xor, actuate_xor};
use algorithms_verus::primitives::bisection::bisection_find;
use algorithms_verus::primitives::reduction::reduce;
use algorithms_verus::primitives::resource_registry::{new_registry, ResourceRegistry};
use algorithms_verus::primitives::sampler::sample_n;
use algorithms_verus::primitives::traversal_engine::traverse;

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
    println!("primitives KAT cross-check (Verus build)");
    let mut all_ok = true;

    // Reduction: additive fold over bounded u64.
    all_ok &= check("reduce(empty)", reduce(&[]), 0);
    all_ok &= check("reduce([1,2,3,4,5])", reduce(&[1, 2, 3, 4, 5]), 15);
    all_ok &= check(
        "reduce(10x 1e9)",
        reduce(&[1_000_000_000u64; 10]),
        10_000_000_000u64,
    );
    all_ok &= check("reduce([42])", reduce(&[42]), 42);

    // ResourceRegistry: bounded indexed storage.
    let mut reg: ResourceRegistry = new_registry(8, 0u64);
    all_ok &= check("new_registry(8).capacity()", reg.capacity(), 8);
    all_ok &= check("new_registry(8)[0] (default 0)", reg.lookup(0), 0);
    reg.register(3, 0xdeadbeefu64);
    all_ok &= check(
        "after register(3, 0xdeadbeef): lookup(3)",
        reg.lookup(3),
        0xdeadbeefu64,
    );
    all_ok &= check("after register(3, ...): lookup(0) frame", reg.lookup(0), 0);
    all_ok &= check("after register(3, ...): lookup(7) frame", reg.lookup(7), 0);

    // TraversalEngine: bounded iteration with budget.
    // Costs [10, 20, 30, 40, 50] with budget 60 → accepts 3 (10+20+30=60), budget=0.
    let r = traverse(&[10u64, 20, 30, 40, 50], 60);
    all_ok &= check("traverse([10,20,30,40,50], 60).accepted", r.0, 3);
    all_ok &= check("traverse([10,20,30,40,50], 60).budget", r.1, 0);
    // Budget exhaust mid-stream: costs [5, 5, 5, 100] with budget 20 → accept 3 (5+5+5=15), budget=5 left,
    // 4th cost 100 doesn't fit so stops.
    let r2 = traverse(&[5u64, 5, 5, 100], 20);
    all_ok &= check("traverse([5,5,5,100], 20).accepted", r2.0, 3);
    all_ok &= check("traverse([5,5,5,100], 20).budget", r2.1, 5);
    // Empty slice: accept 0, budget unchanged.
    let r3 = traverse(&[], 100);
    all_ok &= check("traverse([], 100).accepted", r3.0, 0);
    all_ok &= check("traverse([], 100).budget", r3.1, 100);

    // ActuationPass: per-slot XOR transformation.
    let mut reg2: ResourceRegistry = new_registry(4, 0x00ffu64);
    actuate_xor(&mut reg2, 2, 0xf0f0u64);
    all_ok &= check(
        "actuate_xor(reg, 2, 0xf0f0): pos 2",
        reg2.lookup(2),
        0x00ffu64 ^ 0xf0f0u64,
    );
    all_ok &= check("actuate_xor frame: pos 0", reg2.lookup(0), 0x00ffu64);
    all_ok &= check("actuate_xor frame: pos 3", reg2.lookup(3), 0x00ffu64);
    // Full-pass XOR.
    let mut reg3: ResourceRegistry = new_registry(4, 0u64);
    let masks: Vec<u64> = vec![0x11, 0x22, 0x33, 0x44];
    actuate_pass_xor(&mut reg3, &masks);
    all_ok &= check("actuate_pass_xor: pos 0", reg3.lookup(0), 0x11);
    all_ok &= check("actuate_pass_xor: pos 1", reg3.lookup(1), 0x22);
    all_ok &= check("actuate_pass_xor: pos 2", reg3.lookup(2), 0x33);
    all_ok &= check("actuate_pass_xor: pos 3", reg3.lookup(3), 0x44);

    // Bisection: halving search on sorted slice.
    let sorted: [u64; 7] = [1, 3, 5, 7, 9, 11, 13];
    all_ok &= check("bisection_find(sorted, 1)", bisection_find(&sorted, 1), 0);
    all_ok &= check("bisection_find(sorted, 7)", bisection_find(&sorted, 7), 3);
    all_ok &= check("bisection_find(sorted, 13)", bisection_find(&sorted, 13), 6);
    // Not present: returns sorted.len() (i.e., 7).
    all_ok &= check(
        "bisection_find(sorted, 4) absent",
        bisection_find(&sorted, 4),
        7,
    );
    all_ok &= check(
        "bisection_find(sorted, 100) absent",
        bisection_find(&sorted, 100),
        7,
    );
    // Empty slice: returns 0 (= len).
    all_ok &= check("bisection_find([], 5) empty", bisection_find(&[], 5), 0);

    // Sampler: deterministic-tape sample reduced mod item_count.
    let tape: [u64; 6] = [100, 200, 300, 17, 25, 999];
    let s = sample_n(&tape, 10, 4); // item_count=10, sample_size=4 → first 4 mod 10
    all_ok &= check("sample_n(tape, 10, 4).len()", s.len(), 4);
    all_ok &= check("sample_n[0] = 100 mod 10", s[0], 0);
    all_ok &= check("sample_n[1] = 200 mod 10", s[1], 0);
    all_ok &= check("sample_n[2] = 300 mod 10", s[2], 0);
    all_ok &= check("sample_n[3] = 17 mod 10", s[3], 7);
    // Different modulus.
    let s2 = sample_n(&tape, 7, 5);
    all_ok &= check("sample_n(tape, 7, 5).len()", s2.len(), 5);
    all_ok &= check("sample_n[0] = 100 mod 7", s2[0], 100 % 7);
    all_ok &= check("sample_n[3] = 17 mod 7", s2[3], 17 % 7);
    all_ok &= check("sample_n[4] = 25 mod 7", s2[4], 25 % 7);

    if all_ok {
        println!("KAT_RESULT: SUCCESS (all primitives)");
        std::process::exit(0);
    } else {
        println!("KAT_RESULT: FAIL");
        std::process::exit(1);
    }
}
