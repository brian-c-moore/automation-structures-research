// RFC 8439 §2.5.2 Poly1305 known-answer-test.
extern crate cryptography_verus;
use cryptography_verus::algorithms::mac::poly1305::poly1305_mac;

fn to_hex(bytes: &[u8; 16]) -> String {
    let mut s = String::with_capacity(32);
    for b in bytes.iter() {
        s.push_str(&format!("{:02x}", b));
    }
    s
}

fn main() {
    println!("RFC 8439 §2.5.2 Poly1305 KAT cross-check (Verus build)");
    let key: [u8; 32] = [
        0x85, 0xd6, 0xbe, 0x78, 0x57, 0x55, 0x6d, 0x33, 0x7f, 0x44, 0x52, 0xfe, 0x42, 0xd5, 0x06,
        0xa8, 0x01, 0x03, 0x80, 0x8a, 0xfb, 0x0d, 0xb2, 0xfd, 0x4a, 0xbf, 0xf6, 0xaf, 0x41, 0x49,
        0xf5, 0x1b,
    ];
    let message = b"Cryptographic Forum Research Group";
    let tag = poly1305_mac(&key, message);
    let got = to_hex(&tag);
    let expected = "a8061dc1305136c6c22b8baf0c0127a9";
    if got == expected {
        println!("  PASS  RFC 8439 §2.5.2: {}", expected);
        println!("KAT_RESULT: SUCCESS (1/1)");
        std::process::exit(0);
    } else {
        println!("  FAIL  expected {}, got {}", expected, got);
        println!("KAT_RESULT: FAIL");
        std::process::exit(1);
    }
}
