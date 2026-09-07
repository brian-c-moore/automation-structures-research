//! ChaCha20 known-answer tests (RFC 8439).
//!
//! Input shape (Value::List):
//!   [ Bytes(key:32), Bytes(nonce:12), Int(counter), Bytes(plaintext) ]
//! Output shape:
//!   Bytes(ciphertext)

use crate::test_vectors::Kat;
use crate::value::Value;

pub fn vectors() -> Vec<Kat> {
    // Key = 00 01 02 .. 1F (32 bytes)
    let mut key = [0u8; 32];
    for i in 0..32 {
        key[i] = i as u8;
    }
    let key_vec = key.to_vec();

    // RFC 8439 §2.4.2 nonce: 000000000000004A00000000
    let mut nonce = [0u8; 12];
    nonce[7] = 0x4a;
    let nonce_vec = nonce.to_vec();

    let plaintext = b"Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it.".to_vec();
    let expected = hex_to_bytes("6e2e359a2568f98041ba0728dd0d6981e97e7aec1d4360c20a27afccfd9fae0bf91b65c5524733ab8f593dabcd62b3571639d624e65152ab8f530c359f0861d807ca0dbf500d6a6156a38e088a22b65e52bc514d16ccf806818ce91ab77937365af90bbf74a35be6b40b8eedf2785e42874d");

    vec![Kat {
        name: "rfc8439-section-2.4.2-sunscreen",
        source: "RFC 8439 §2.4.2 (canonical ChaCha20 encryption vector)",
        algo: "chacha20",
        input: Value::List(vec![
            Value::Bytes(key_vec.clone()),
            Value::Bytes(nonce_vec.clone()),
            Value::Int(1),
            Value::Bytes(plaintext),
        ]),
        expected: Value::Bytes(expected),
    }]
}

fn hex_to_bytes(s: &str) -> Vec<u8> {
    crate::value::hex_decode(s).expect("invalid hex in chacha20 test vector")
}
