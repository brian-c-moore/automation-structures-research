// RFC 8032 §7.1 Ed25519 known-answer-test (verify only).
extern crate cryptography_verus;
use cryptography_verus::algorithms::asymmetric::ed25519::ed25519_verify;

fn from_hex(s: &str) -> Vec<u8> {
    let mut out = Vec::with_capacity(s.len() / 2);
    let bytes = s.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        let hi = match bytes[i] {
            b'0'..=b'9' => bytes[i] - b'0',
            b'a'..=b'f' => bytes[i] - b'a' + 10,
            b'A'..=b'F' => bytes[i] - b'A' + 10,
            _ => 0,
        };
        let lo = match bytes[i + 1] {
            b'0'..=b'9' => bytes[i + 1] - b'0',
            b'a'..=b'f' => bytes[i + 1] - b'a' + 10,
            b'A'..=b'F' => bytes[i + 1] - b'A' + 10,
            _ => 0,
        };
        out.push((hi << 4) | lo);
        i += 2;
    }
    out
}

fn to_arr32(v: &[u8]) -> [u8; 32] {
    let mut a = [0u8; 32];
    for i in 0..32 {
        a[i] = v[i];
    }
    a
}

fn to_arr64(v: &[u8]) -> [u8; 64] {
    let mut a = [0u8; 64];
    for i in 0..64 {
        a[i] = v[i];
    }
    a
}

fn check_pass(name: &str, pk_hex: &str, msg: &[u8], sig_hex: &str) -> bool {
    let pk = to_arr32(&from_hex(pk_hex));
    let sig = to_arr64(&from_hex(sig_hex));
    let ok = ed25519_verify(&pk, msg, &sig);
    if ok {
        println!("  PASS  {}", name);
    } else {
        println!("  FAIL  {} (expected valid, verify returned false)", name);
    }
    ok
}

fn main() {
    println!("RFC 8032 §7.1 Ed25519 KAT cross-check (Verus build)");
    let mut all_ok = true;

    // RFC 8032 §7.1 Test 1
    all_ok &= check_pass(
        "RFC 8032 §7.1 test 1 (empty message)",
        "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a",
        b"",
        "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b",
    );

    // RFC 8032 §7.1 Test 2
    all_ok &= check_pass(
        "RFC 8032 §7.1 test 2 (1-byte message)",
        "3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c",
        &[0x72],
        "92a009a9f0d4cab8720e820b5f642540a2b27b5416503f8fb3762223ebdb69da085ac1e43e15996e458f3613d0f11d8c387b2eaeb4302aeeb00d291612bb0c00",
    );

    if all_ok {
        println!("KAT_RESULT: SUCCESS (2/2)");
        std::process::exit(0);
    } else {
        println!("KAT_RESULT: FAIL");
        std::process::exit(1);
    }
}
