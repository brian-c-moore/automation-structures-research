// RFC 7748 §5.2 X25519 known-answer-test.
extern crate cryptography_verus;
use cryptography_verus::algorithms::asymmetric::x25519::x25519;

fn to_hex(bytes: &[u8; 32]) -> String {
    let mut s = String::with_capacity(64);
    for b in bytes.iter() {
        s.push_str(&format!("{:02x}", b));
    }
    s
}

fn from_hex(s: &str) -> [u8; 32] {
    let mut out = [0u8; 32];
    let bytes = s.as_bytes();
    for i in 0..32 {
        let hi = match bytes[2 * i] {
            b'0'..=b'9' => bytes[2 * i] - b'0',
            b'a'..=b'f' => bytes[2 * i] - b'a' + 10,
            _ => 0,
        };
        let lo = match bytes[2 * i + 1] {
            b'0'..=b'9' => bytes[2 * i + 1] - b'0',
            b'a'..=b'f' => bytes[2 * i + 1] - b'a' + 10,
            _ => 0,
        };
        out[i] = (hi << 4) | lo;
    }
    out
}

fn check(name: &str, scalar_hex: &str, u_hex: &str, expected: &str) -> bool {
    let scalar = from_hex(scalar_hex);
    let u = from_hex(u_hex);
    let out = x25519(&scalar, &u);
    let got = to_hex(&out);
    let ok = got == expected;
    if ok {
        println!("  PASS  {}: {}", name, expected);
    } else {
        println!("  FAIL  {}: expected {}, got {}", name, expected, got);
    }
    ok
}

fn main() {
    println!("RFC 7748 §5.2 X25519 KAT cross-check (Verus build)");
    let mut all_ok = true;

    // RFC 7748 §5.2 Test Vector 1
    all_ok &= check(
        "RFC 7748 §5.2 test 1",
        "a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4",
        "e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c",
        "c3da55379de9c6908e94ea4df28d084f32eccf03491c71f754b4075577a28552",
    );

    // RFC 7748 §5.2 Test Vector 2
    all_ok &= check(
        "RFC 7748 §5.2 test 2",
        "4b66e9d4d1b4673c5ad22691957d6af5c11b6421e0ea01d42ca4169e7918ba0d",
        "e5210f12786811d3f4b7959d0538ae2c31dbe7106fc03c3efc4cd549c715a493",
        "95cbde9476e8907d7aade45cb4b873f88b595a68799fa152e6f8f7647aac7957",
    );

    if all_ok {
        println!("KAT_RESULT: SUCCESS (2/2)");
        std::process::exit(0);
    } else {
        println!("KAT_RESULT: FAIL");
        std::process::exit(1);
    }
}
