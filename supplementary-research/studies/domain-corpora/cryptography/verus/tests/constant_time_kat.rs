// constant-time KAT — cross-check. Each CT-discipline module
// is exercised with hand-picked inputs verifying:
//   1. functional equivalence (CT output == VT/spec output).
//   2. (Structural CT timing property is verified at source-shape level.)
extern crate cryptography_verus;
use cryptography_verus::constant_time::bitsliced_aes_ct::bitsliced_aes_ct_realization;
use cryptography_verus::constant_time::ct_select::{ct_select_u64, ct_select_u8};
use cryptography_verus::constant_time::functionally_equivalent::ladder_equivalent;
use cryptography_verus::constant_time::sig_equality::ct_eq_bytes;
use cryptography_verus::constant_time::x25519_ladder::{
    ct_cswap_u64, x25519_ladder_ct_realization,
};

fn check(name: &str, ok: bool) -> bool {
    if ok {
        println!("  PASS  {}", name);
    } else {
        println!("  FAIL  {}", name);
    }
    ok
}

fn main() {
    println!("constant-time KAT (Verus build)");
    let mut all_ok = true;

    // Montgomery-ladder CT/VT equivalence.
    let (ct, vt) = ladder_equivalent();
    all_ok &= check("functionally_equivalent: ct.0 == vt.0", ct.0 == vt.0);
    all_ok &= check("functionally_equivalent: ct.1 == vt.1", ct.1 == vt.1);

    // X25519 ladder CT.
    let scalar = [0x42u8; 32];
    let base = [0x09u8; 32];
    let (xct, xvt) = x25519_ladder_ct_realization(&scalar, &base);
    all_ok &= check("x25519_ladder_ct: ct == vt", xct == xvt);

    // ct_cswap_u64.
    let (a, b) = ct_cswap_u64(0xAAAA, 0xBBBB, 1);
    all_ok &= check("ct_cswap_u64(_, _, 1) swaps", a == 0xBBBB && b == 0xAAAA);
    let (a, b) = ct_cswap_u64(0xAAAA, 0xBBBB, 0);
    all_ok &= check("ct_cswap_u64(_, _, 0) no swap", a == 0xAAAA && b == 0xBBBB);

    // Bitsliced AES CT.
    let key = [0u8; 16];
    let pt = [0u8; 16];
    let (act, avt) = bitsliced_aes_ct_realization(&key, &pt);
    all_ok &= check("bitsliced_aes_ct: ct == vt", act == avt);

    // ct_select.
    all_ok &= check(
        "ct_select_u64(1, a, b) = a",
        ct_select_u64(1, 0xAAAA, 0xBBBB) == 0xAAAA,
    );
    all_ok &= check(
        "ct_select_u64(0, a, b) = b",
        ct_select_u64(0, 0xAAAA, 0xBBBB) == 0xBBBB,
    );
    all_ok &= check(
        "ct_select_u8(1, a, b) = a",
        ct_select_u8(1, 0xAB, 0xCD) == 0xAB,
    );
    all_ok &= check(
        "ct_select_u8(0, a, b) = b",
        ct_select_u8(0, 0xAB, 0xCD) == 0xCD,
    );

    // ct_eq_bytes.
    all_ok &= check("ct_eq_bytes(equal)", ct_eq_bytes(b"abc", b"abc") == 1);
    all_ok &= check("ct_eq_bytes(diff at 0)", ct_eq_bytes(b"abc", b"xbc") == 0);
    all_ok &= check("ct_eq_bytes(diff at 2)", ct_eq_bytes(b"abc", b"abx") == 0);

    if all_ok {
        println!("KAT_RESULT: SUCCESS (4/4 CT-discipline modules at )");
        std::process::exit(0);
    } else {
        println!("KAT_RESULT: FAIL");
        std::process::exit(1);
    }
}
