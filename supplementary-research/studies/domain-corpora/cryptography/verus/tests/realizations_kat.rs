// realizations KAT — cross-check. Each realization module's
// exec returns (base_output, realized_output). The refinement claim
// is realized == base; this KAT verifies it on hand-picked inputs.
extern crate cryptography_verus;
use cryptography_verus::realizations::bitsliced::parallel_refinement;
use cryptography_verus::realizations::bitsliced_aes::bitsliced_aes_realization;
use cryptography_verus::realizations::bitsliced_keccak::bitsliced_keccak_realization;
use cryptography_verus::realizations::hardware_accelerated::hw_refinement;
use cryptography_verus::realizations::pclmulqdq::pclmulqdq_realization;
use cryptography_verus::realizations::sha_ni::sha_ni_realization;
use cryptography_verus::realizations::simd_aes_ctr::simd_aes_ctr_realization;
use cryptography_verus::realizations::simd_lane_batched::simd_refinement;
use cryptography_verus::realizations::simd_poly1305::simd_poly1305_realization;

fn check(name: &str, ok: bool) -> bool {
    if ok {
        println!("  PASS  {}", name);
    } else {
        println!("  FAIL  {}", name);
    }
    ok
}

fn main() {
    println!("realizations KAT (Verus build)");
    let mut all_ok = true;

    // Lockstep refinement specs.
    let (base1, real1) = parallel_refinement(3);
    all_ok &= check("parallel_refinement: base == realized", base1 == real1);
    let (base2, real2) = hw_refinement(3);
    all_ok &= check("hw_refinement: base == realized", base2 == real2);
    let (base3, real3) = simd_refinement(3);
    all_ok &= check("simd_refinement: base == realized", base3 == real3);

    // Per-algorithm realizations (each wraps a base algorithm).
    let key = [0u8; 16];
    let pt = [0u8; 16];
    let (b, r) = bitsliced_aes_realization(&key, &pt);
    all_ok &= check("bitsliced_aes_realization == base", b == r);

    let (b, r) = bitsliced_keccak_realization(b"abc");
    all_ok &= check("bitsliced_keccak_realization == base", b == r);

    let (b, r) = sha_ni_realization(b"abc");
    all_ok &= check("sha_ni_realization == base", b == r);

    all_ok &= check("pclmulqdq_realization", pclmulqdq_realization());

    let iv = [0u8; 16];
    let pt = [0u8; 32];
    let (b, r) = simd_aes_ctr_realization(&key, &iv, &pt);
    all_ok &= check("simd_aes_ctr_realization == base", b == r);

    let pk = [0u8; 32];
    let (b, r) = simd_poly1305_realization(&pk, b"hello world");
    all_ok &= check("simd_poly1305_realization == base", b == r);

    if all_ok {
        println!("KAT_RESULT: SUCCESS (9/9 realization modules at )");
        std::process::exit(0);
    } else {
        println!("KAT_RESULT: FAIL");
        std::process::exit(1);
    }
}
