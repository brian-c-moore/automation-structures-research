// FIPS 180-4 known-answer-test (KAT) cross-check for the Verus-verified
// SHA-256 implementation in cryptography_verus::algorithms::hashes::sha256.
//
// This binary links against the compiled cryptography_verus rlib and
// exercises the SHA-256 function against the three FIPS 180-4 published
// test vectors (Appendix B). The module carries the KAT cross-check only
// while this binary returns success.

extern crate cryptography_verus;
use cryptography_verus::algorithms::hashes::sha256::sha256;

fn to_hex(bytes: &[u8; 32]) -> String {
    let mut s = String::with_capacity(64);
    for b in bytes.iter() {
        s.push_str(&format!("{:02x}", b));
    }
    s
}

fn check(name: &str, msg: &[u8], expected: &str) -> bool {
    let got = to_hex(&sha256(msg));
    let ok = got == expected;
    if ok {
        println!("  PASS  {}: {}", name, expected);
    } else {
        println!("  FAIL  {}: expected {}, got {}", name, expected, got);
    }
    ok
}

fn main() {
    println!("FIPS 180-4 SHA-256 KAT cross-check (Verus build)");
    let mut all_ok = true;
    all_ok &= check(
        "empty",
        b"",
        "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
    );
    all_ok &= check(
        "abc (FIPS 180-4 Appendix B.1)",
        b"abc",
        "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
    );
    all_ok &= check(
        "448-bit message (FIPS 180-4 Appendix B.2)",
        b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
        "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1",
    );
    if all_ok {
        println!("KAT_RESULT: SUCCESS (3/3)");
        std::process::exit(0);
    } else {
        println!("KAT_RESULT: FAIL");
        std::process::exit(1);
    }
}
