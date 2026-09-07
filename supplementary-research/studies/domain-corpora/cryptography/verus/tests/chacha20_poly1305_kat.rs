// RFC 8439 §2.8.2 ChaCha20-Poly1305 AEAD known-answer-test.
extern crate cryptography_verus;
use cryptography_verus::algorithms::aead::chacha20_poly1305::chacha20_poly1305_encrypt;

fn to_hex(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        s.push_str(&format!("{:02x}", b));
    }
    s
}

fn main() {
    println!("RFC 8439 §2.8.2 ChaCha20-Poly1305 KAT cross-check (Verus build)");

    let key: [u8; 32] = [
        0x80, 0x81, 0x82, 0x83, 0x84, 0x85, 0x86, 0x87, 0x88, 0x89, 0x8a, 0x8b, 0x8c, 0x8d, 0x8e,
        0x8f, 0x90, 0x91, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97, 0x98, 0x99, 0x9a, 0x9b, 0x9c, 0x9d,
        0x9e, 0x9f,
    ];
    let nonce: [u8; 12] = [
        0x07, 0x00, 0x00, 0x00, 0x40, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47,
    ];
    let aad: Vec<u8> = vec![
        0x50, 0x51, 0x52, 0x53, 0xc0, 0xc1, 0xc2, 0xc3, 0xc4, 0xc5, 0xc6, 0xc7,
    ];
    let plaintext = b"Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it.";

    let expected_ct = "d31a8d34648e60db7b86afbc53ef7ec2a4aded51296e08fea9e2b5a736ee62d63dbea45e8ca9671282fafb69da92728b1a71de0a9e060b2905d6a5b67ecd3b3692ddbd7f2d778b8c9803aee328091b58fab324e4fad675945585808b4831d7bc3ff4def08e4b7a9de576d26586cec64b6116";
    let expected_tag = "1ae10b594f09e26a7e902ecbd0600691";

    let (ct, tag) = chacha20_poly1305_encrypt(&key, &nonce, &aad, plaintext);
    let got_ct = to_hex(&ct);
    let got_tag = to_hex(&tag);

    let mut all_ok = true;
    if got_ct == expected_ct {
        println!("  PASS  ciphertext: {}", expected_ct);
    } else {
        println!(
            "  FAIL  ciphertext: expected {} got {}",
            expected_ct, got_ct
        );
        all_ok = false;
    }
    if got_tag == expected_tag {
        println!("  PASS  tag: {}", expected_tag);
    } else {
        println!("  FAIL  tag: expected {} got {}", expected_tag, got_tag);
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
