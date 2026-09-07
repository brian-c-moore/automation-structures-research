// FIPS 197 Appendix C.1 known-answer-test for the Verus AES-128 build.
extern crate cryptography_verus;
use cryptography_verus::algorithms::symmetric::aes128::aes128_encrypt_block;

fn to_hex(bytes: &[u8; 16]) -> String {
    let mut s = String::with_capacity(32);
    for b in bytes.iter() {
        s.push_str(&format!("{:02x}", b));
    }
    s
}

fn check(name: &str, key: [u8; 16], pt: [u8; 16], expected: &str) -> bool {
    let ct = aes128_encrypt_block(&key, &pt);
    let got = to_hex(&ct);
    let ok = got == expected;
    if ok {
        println!("  PASS  {}: {}", name, expected);
    } else {
        println!("  FAIL  {}: expected {}, got {}", name, expected, got);
    }
    ok
}

fn main() {
    println!("FIPS 197 AES-128 KAT cross-check (Verus build)");
    let mut all_ok = true;

    // FIPS 197 Appendix C.1
    let key1: [u8; 16] = [
        0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e,
        0x0f,
    ];
    let pt1: [u8; 16] = [
        0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee,
        0xff,
    ];
    all_ok &= check(
        "FIPS 197 Appendix C.1",
        key1,
        pt1,
        "69c4e0d86a7b0430d8cdb78070b4c55a",
    );

    if all_ok {
        println!("KAT_RESULT: SUCCESS (1/1)");
        std::process::exit(0);
    } else {
        println!("KAT_RESULT: FAIL");
        std::process::exit(1);
    }
}
