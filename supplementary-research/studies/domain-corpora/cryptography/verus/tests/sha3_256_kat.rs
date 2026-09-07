// FIPS 202 / NIST CAVP known-answer-test cross-check for the Verus-
// verified SHA-3-256 implementation in
// cryptography_verus::algorithms::hashes::sha3_256.

extern crate cryptography_verus;
use cryptography_verus::algorithms::hashes::sha3_256::sha3_256;

fn to_hex(bytes: &[u8; 32]) -> String {
    let mut s = String::with_capacity(64);
    for b in bytes.iter() {
        s.push_str(&format!("{:02x}", b));
    }
    s
}

fn check(name: &str, msg: &[u8], expected: &str) -> bool {
    let got = to_hex(&sha3_256(msg));
    let ok = got == expected;
    if ok {
        println!("  PASS  {}: {}", name, expected);
    } else {
        println!("  FAIL  {}: expected {}, got {}", name, expected, got);
    }
    ok
}

fn main() {
    println!("FIPS 202 / NIST CAVP SHA-3-256 KAT cross-check (Verus build)");
    let mut all_ok = true;
    all_ok &= check(
        "empty (NIST CAVP)",
        b"",
        "a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a",
    );
    all_ok &= check(
        "abc (NIST CAVP)",
        b"abc",
        "3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe24511431532",
    );
    all_ok &= check(
        "448-bit message (NIST CAVP)",
        b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
        "41c0dba2a9d6240849100376a8235e2c82e1b9998a999e21db32dd97496d3376",
    );
    if all_ok {
        println!("KAT_RESULT: SUCCESS (3/3)");
        std::process::exit(0);
    } else {
        println!("KAT_RESULT: FAIL");
        std::process::exit(1);
    }
}
