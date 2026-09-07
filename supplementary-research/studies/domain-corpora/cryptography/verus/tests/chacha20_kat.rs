// RFC 8439 §A.2 ChaCha20 known-answer-test (Test Vector #1).
extern crate cryptography_verus;
use cryptography_verus::algorithms::symmetric::chacha20::chacha20_encrypt;

fn to_hex_vec(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        s.push_str(&format!("{:02x}", b));
    }
    s
}

fn main() {
    println!("RFC 8439 §A.2 ChaCha20 KAT cross-check (Verus build)");
    let mut all_ok = true;

    // Test Vector #1 (RFC 8439 §A.2): all-zero key/nonce/plaintext.
    let key: [u8; 32] = [0u8; 32];
    let nonce: [u8; 12] = [0u8; 12];
    let plaintext: Vec<u8> = vec![0u8; 64];
    let expected = "76b8e0ada0f13d90405d6ae55386bd28bdd219b8a08ded1aa836efcc8b770dc7da41597c5157488d7724e03fb8d84a376a43b8f41518a11cc387b669b2ee6586";

    let ct = chacha20_encrypt(&key, 0, &nonce, &plaintext);
    let got = to_hex_vec(&ct);
    if got == expected {
        println!("  PASS  RFC 8439 §A.2 Test Vector #1");
        println!("    {}", expected);
    } else {
        println!("  FAIL  expected {}", expected);
        println!("    got {}", got);
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
