//! SHA-3-256 known-answer tests.
//!
//! Source: FIPS 202 / NIST CAVP canonical small-message vectors.

use crate::test_vectors::Kat;
use crate::value::Value;

pub fn vectors() -> Vec<Kat> {
    vec![
        Kat {
            name: "empty-string",
            source: "NIST CAVP / FIPS 202 canonical empty-input vector",
            algo: "sha3_256",
            input: Value::Bytes(b"".to_vec()),
            expected: Value::bytes_hex(
                "a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a",
            ),
        },
        Kat {
            name: "abc",
            source: "NIST CAVP SHA-3-256 ShortMsg KAT (24-bit input \"abc\")",
            algo: "sha3_256",
            input: Value::Bytes(b"abc".to_vec()),
            expected: Value::bytes_hex(
                "3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe24511431532",
            ),
        },
        Kat {
            name: "448-bit-msg",
            source: "NIST CAVP SHA-3-256 ShortMsg KAT (448-bit standard test message)",
            algo: "sha3_256",
            input: Value::Bytes(
                b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq".to_vec(),
            ),
            expected: Value::bytes_hex(
                "41c0dba2a9d6240849100376a8235e2c82e1b9998a999e21db32dd97496d3376",
            ),
        },
    ]
}
