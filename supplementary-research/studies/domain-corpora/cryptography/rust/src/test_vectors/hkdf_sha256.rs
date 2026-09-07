//! HKDF-SHA-256 known-answer tests (RFC 5869 Appendix A).
//!
//! Input shape (Value::List):
//!   [ Bytes(salt), Bytes(ikm), Bytes(info), Int(length) ]
//! Output shape:
//!   Bytes(OKM)

use crate::test_vectors::Kat;
use crate::value::Value;

pub fn vectors() -> Vec<Kat> {
    vec![
        Kat {
            name: "rfc5869-a.1-basic-sha256",
            source: "RFC 5869 Appendix A.1 (basic test case with SHA-256)",
            algo: "hkdf_sha256",
            input: Value::List(vec![
                Value::Bytes(vec![
                    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
                    0x08, 0x09, 0x0a, 0x0b, 0x0c,
                ]),
                Value::Bytes(vec![0x0b; 22]),
                Value::Bytes(vec![
                    0xf0, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8, 0xf9,
                ]),
                Value::Int(42),
            ]),
            expected: Value::bytes_hex(
                "3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf34007208d5b887185865",
            ),
        },
        Kat {
            name: "rfc5869-a.3-zero-length-salt-info",
            source: "RFC 5869 Appendix A.3 (test with zero-length salt and info)",
            algo: "hkdf_sha256",
            input: Value::List(vec![
                Value::Bytes(Vec::new()),
                Value::Bytes(vec![0x0b; 22]),
                Value::Bytes(Vec::new()),
                Value::Int(42),
            ]),
            expected: Value::bytes_hex(
                "8da4e775a563c18f715f802a063c5a31b8a11f5c5ee1879ec3454e5f3c738d2d9d201395faa4b61a96c8",
            ),
        },
    ]
}
