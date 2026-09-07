// NIST SP 800-38D Appendix B Test Case 3 AES-128-GCM known-answer-test.
extern crate cryptography_verus;
use cryptography_verus::algorithms::aead::aes128_gcm::aes128_gcm_encrypt;

fn to_hex(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        s.push_str(&format!("{:02x}", b));
    }
    s
}

fn main() {
    println!("NIST SP 800-38D Appendix B Test Case 3 AES-128-GCM KAT cross-check (Verus build)");

    // Test Case 3
    let key: [u8; 16] = [
        0xfe, 0xff, 0xe9, 0x92, 0x86, 0x65, 0x73, 0x1c, 0x6d, 0x6a, 0x8f, 0x94, 0x67, 0x30, 0x83,
        0x08,
    ];
    let iv: [u8; 12] = [
        0xca, 0xfe, 0xba, 0xbe, 0xfa, 0xce, 0xdb, 0xad, 0xde, 0xca, 0xf8, 0x88,
    ];
    let aad: Vec<u8> = vec![];
    let plaintext: Vec<u8> = vec![
        0xd9, 0x31, 0x32, 0x25, 0xf8, 0x84, 0x06, 0xe5, 0xa5, 0x59, 0x09, 0xc5, 0xaf, 0xf5, 0x26,
        0x9a, 0x86, 0xa7, 0xa9, 0x53, 0x15, 0x34, 0xf7, 0xda, 0x2e, 0x4c, 0x30, 0x3d, 0x8a, 0x31,
        0x8a, 0x72, 0x1c, 0x3c, 0x0c, 0x95, 0x95, 0x68, 0x09, 0x53, 0x2f, 0xcf, 0x0e, 0x24, 0x49,
        0xa6, 0xb5, 0x25, 0xb1, 0x6a, 0xed, 0xf5, 0xaa, 0x0d, 0xe6, 0x57, 0xba, 0x63, 0x7b, 0x39,
        0x1a, 0xaf, 0xd2, 0x55,
    ];
    let expected_ct = "42831ec2217774244b7221b784d0d49ce3aa212f2c02a4e035c17e2329aca12e21d514b25466931c7d8f6a5aac84aa051ba30b396a0aac973d58e091473f5985";
    let expected_tag = "4d5c2af327cd64a62cf35abd2ba6fab4";

    let (ct, tag) = aes128_gcm_encrypt(&key, &iv, &aad, &plaintext);
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
