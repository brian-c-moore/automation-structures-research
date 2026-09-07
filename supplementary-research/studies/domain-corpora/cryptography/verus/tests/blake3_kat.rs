// BLAKE3 official test_vectors.json cross-check for the Verus-verified
// BLAKE3 implementation in cryptography_verus::algorithms::hashes::blake3.

extern crate cryptography_verus;
use cryptography_verus::algorithms::hashes::blake3::blake3_hash;

fn to_hex(bytes: &[u8; 32]) -> String {
    let mut s = String::with_capacity(64);
    for b in bytes.iter() {
        s.push_str(&format!("{:02x}", b));
    }
    s
}

fn check(name: &str, msg: &[u8], expected: &str) -> bool {
    let got = to_hex(&blake3_hash(msg));
    let ok = got == expected;
    if ok {
        println!("  PASS  {}: {}", name, expected);
    } else {
        println!("  FAIL  {}: expected {}, got {}", name, expected, got);
    }
    ok
}

fn main() {
    println!("BLAKE3 official test_vectors.json cross-check (Verus build)");
    let mut all_ok = true;
    all_ok &= check(
        "empty input (length 0)",
        b"",
        "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262",
    );
    all_ok &= check(
        "abc (single-block path)",
        b"abc",
        "6437b3ac38465133ffb63b75273a8db548c558465d79db03fd359c6cd5bd9d85",
    );
    if all_ok {
        println!("KAT_RESULT: SUCCESS (2/2)");
        std::process::exit(0);
    } else {
        println!("KAT_RESULT: FAIL");
        std::process::exit(1);
    }
}
