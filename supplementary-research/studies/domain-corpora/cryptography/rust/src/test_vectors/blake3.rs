//! BLAKE3 known-answer tests.
//!
//! Source: the official BLAKE3 reference test vectors at
//! https://github.com/BLAKE3-team/BLAKE3/blob/master/test_vectors/test_vectors.json
//! plus the well-known "abc" vector.
//!
//! The full reference test set parameterises input by length and uses a
//! specific input pattern (`input[i] = i % 251`). The vendored vectors
//! below cover exactly empty input and "abc". No broader length coverage
//! is claimed.

use crate::test_vectors::Kat;
use crate::value::Value;

pub fn vectors() -> Vec<Kat> {
    vec![
        Kat {
            name: "empty-string",
            source: "BLAKE3 test_vectors.json (input length 0)",
            algo: "blake3",
            input: Value::Bytes(b"".to_vec()),
            expected: Value::bytes_hex(
                "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262",
            ),
        },
        Kat {
            name: "abc",
            source: "BLAKE3 reference (well-known short-message vector)",
            algo: "blake3",
            input: Value::Bytes(b"abc".to_vec()),
            expected: Value::bytes_hex(
                "6437b3ac38465133ffb63b75273a8db548c558465d79db03fd359c6cd5bd9d85",
            ),
        },
    ]
}
