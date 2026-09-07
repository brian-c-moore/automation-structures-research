//! HMAC-SHA-256 known-answer tests (RFC 4231 §4).
//!
//! Input shape (Value::List):
//!   [ Bytes(key), Bytes(message) ]
//! Output shape:
//!   Bytes(tag:32)

use crate::test_vectors::Kat;
use crate::value::Value;

pub fn vectors() -> Vec<Kat> {
    vec![
        Kat {
            name: "rfc4231-test-1",
            source: "RFC 4231 §4.2 (20-byte 0x0b key, \"Hi There\")",
            algo: "hmac_sha256",
            input: Value::List(vec![
                Value::Bytes(vec![0x0b; 20]),
                Value::Bytes(b"Hi There".to_vec()),
            ]),
            expected: Value::bytes_hex(
                "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7",
            ),
        },
        Kat {
            name: "rfc4231-test-2",
            source: "RFC 4231 §4.3 (\"Jefe\" key, \"what do ya want for nothing?\")",
            algo: "hmac_sha256",
            input: Value::List(vec![
                Value::Bytes(b"Jefe".to_vec()),
                Value::Bytes(b"what do ya want for nothing?".to_vec()),
            ]),
            expected: Value::bytes_hex(
                "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843",
            ),
        },
        Kat {
            name: "rfc4231-test-3",
            source: "RFC 4231 §4.4 (20-byte 0xaa key, 50-byte 0xdd msg)",
            algo: "hmac_sha256",
            input: Value::List(vec![
                Value::Bytes(vec![0xaa; 20]),
                Value::Bytes(vec![0xdd; 50]),
            ]),
            expected: Value::bytes_hex(
                "773ea91e36800e46854db8ebd09181a72959098b3ef8c122d9635514ced565fe",
            ),
        },
        Kat {
            name: "rfc4231-test-5",
            source: "RFC 4231 §4.6 (20-byte 0x0c key, \"Test With Truncation\" msg; full output)",
            algo: "hmac_sha256",
            input: Value::List(vec![
                Value::Bytes(vec![0x0c; 20]),
                Value::Bytes(b"Test With Truncation".to_vec()),
            ]),
            expected: Value::bytes_hex(
                "a3b6167473100ee06e0c796c2955552bfa6f7c0a6a8aef8b93f860aab0cd20c5",
            ),
        },
    ]
}
