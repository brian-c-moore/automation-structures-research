// RFC 7914 §11 PBKDF2-HMAC-SHA-256 known-answer-test (small iter counts).
extern crate cryptography_verus;
use cryptography_verus::algorithms::kdf::pbkdf2_hmac_sha256::pbkdf2_hmac_sha256;

fn to_hex(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        s.push_str(&format!("{:02x}", b));
    }
    s
}

fn main() {
    println!("RFC 7914 §11 PBKDF2-HMAC-SHA-256 KAT cross-check (Verus build)");
    let mut all_ok = true;

    // RFC 7914 §11: pbkdf2_hmac_sha256("passwd", "salt", 1, 64) =
    let dk1 = pbkdf2_hmac_sha256(b"passwd", b"salt", 1, 64);
    let got1 = to_hex(&dk1);
    let expected1 = "55ac046e56e3089fec1691c22544b605f94185216dde0465e68b9d57c20dacbc49ca9cccf179b645991664b39d77ef317c71b845b1e30bd509112041d3a19783";
    if got1 == expected1 {
        println!("  PASS  RFC 7914 §11 (iterations=1, dkLen=64)");
        println!("    {}", expected1);
    } else {
        println!("  FAIL  expected {}", expected1);
        println!("    got {}", got1);
        all_ok = false;
    }

    if all_ok {
        println!("KAT_RESULT: SUCCESS (1/1)");
        std::process::exit(0);
    } else {
        println!("KAT_RESULT: FAIL");
        std::process::exit(1);
    }
}
