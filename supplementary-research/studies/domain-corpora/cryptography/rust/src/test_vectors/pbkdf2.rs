//! PBKDF2-HMAC-SHA-256 known-answer tests.
//!
//! Input shape (Value::List):
//!   [ Bytes(password), Bytes(salt), Int(iterations), Int(length) ]
//! Output shape:
//!   Bytes(DK)

use crate::test_vectors::Kat;
use crate::value::Value;

pub fn vectors() -> Vec<Kat> {
    vec![
        Kat {
            name: "rfc7914-11-passwd-salt-c1-len64",
            source: "RFC 7914 §11 (PBKDF2-HMAC-SHA-256 with c=1, dkLen=64)",
            algo: "pbkdf2_hmac_sha256",
            input: Value::List(vec![
                Value::Bytes(b"passwd".to_vec()),
                Value::Bytes(b"salt".to_vec()),
                Value::Int(1),
                Value::Int(64),
            ]),
            expected: Value::bytes_hex(
                "55ac046e56e3089fec1691c22544b605f94185216dde0465e68b9d57c20dacbc49ca9cccf179b645991664b39d77ef317c71b845b1e30bd509112041d3a19783",
            ),
        },
    ]
}
