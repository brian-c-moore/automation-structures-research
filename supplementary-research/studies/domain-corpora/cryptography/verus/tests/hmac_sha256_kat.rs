// RFC 4231 HMAC-SHA-256 known-answer-test.
extern crate cryptography_verus;
use cryptography_verus::algorithms::mac::hmac_sha256::hmac_sha256;

fn to_hex(bytes: &[u8; 32]) -> String {
    let mut s = String::with_capacity(64);
    for b in bytes.iter() {
        s.push_str(&format!("{:02x}", b));
    }
    s
}

fn check(name: &str, key: &[u8], message: &[u8], expected: &str) -> bool {
    let mac = hmac_sha256(key, message);
    let got = to_hex(&mac);
    let ok = got == expected;
    if ok {
        println!("  PASS  {}: {}", name, expected);
    } else {
        println!("  FAIL  {}: expected {}, got {}", name, expected, got);
    }
    ok
}

fn main() {
    println!("RFC 4231 HMAC-SHA-256 KAT cross-check (Verus build)");
    let mut all_ok = true;
    // Test Case 1
    let key1 = [0x0bu8; 20];
    all_ok &= check(
        "RFC 4231 Test Case 1",
        &key1,
        b"Hi There",
        "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7",
    );
    // Test Case 2
    let key2 = b"Jefe";
    all_ok &= check(
        "RFC 4231 Test Case 2",
        key2,
        b"what do ya want for nothing?",
        "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843",
    );
    if all_ok {
        println!("KAT_RESULT: SUCCESS (2/2)");
        std::process::exit(0);
    } else {
        println!("KAT_RESULT: FAIL");
        std::process::exit(1);
    }
}
