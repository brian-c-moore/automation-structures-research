// RFC 5869 Appendix A HKDF-SHA-256 known-answer-test.
extern crate cryptography_verus;
use cryptography_verus::algorithms::kdf::hkdf_sha256::hkdf_sha256;

fn to_hex(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        s.push_str(&format!("{:02x}", b));
    }
    s
}

fn main() {
    println!("RFC 5869 Appendix A HKDF-SHA-256 KAT cross-check (Verus build)");
    let mut all_ok = true;

    // A.1
    let ikm1: Vec<u8> = vec![0x0bu8; 22];
    let salt1: Vec<u8> = (0..13).map(|i| i as u8).collect();
    let info1: Vec<u8> = (0xf0..=0xf9).collect();
    let okm1 = hkdf_sha256(&salt1, &ikm1, &info1, 42);
    let got1 = to_hex(&okm1);
    let expected1 =
        "3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf34007208d5b887185865";
    if got1 == expected1 {
        println!("  PASS  A.1: {}", expected1);
    } else {
        println!("  FAIL  A.1: expected {}, got {}", expected1, got1);
        all_ok = false;
    }

    // A.3 (no salt, no info)
    let ikm3: Vec<u8> = vec![0x0bu8; 22];
    let okm3 = hkdf_sha256(&[], &ikm3, &[], 42);
    let got3 = to_hex(&okm3);
    let expected3 =
        "8da4e775a563c18f715f802a063c5a31b8a11f5c5ee1879ec3454e5f3c738d2d9d201395faa4b61a96c8";
    if got3 == expected3 {
        println!("  PASS  A.3: {}", expected3);
    } else {
        println!("  FAIL  A.3: expected {}, got {}", expected3, got3);
        all_ok = false;
    }

    if all_ok {
        println!("KAT_RESULT: SUCCESS (2/2)");
        std::process::exit(0);
    } else {
        println!("KAT_RESULT: FAIL");
        std::process::exit(1);
    }
}
