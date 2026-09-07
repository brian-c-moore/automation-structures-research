//! SHA-256 known-answer tests.
//!
//! Vectors held here: FIPS 180-4 Appendix B (the canonical "abc" and the
//! 448-bit example) plus the NIST CAVP empty-string vector. These three
//! are the ones independently verified against the published standard's
//! appendices; the larger NIST CAVP sets (SHA-2 Monte Carlo vectors,
//! variable-length short-message KATs) are not vendored.

use crate::test_vectors::Kat;
use crate::value::Value;

pub fn vectors() -> Vec<Kat> {
    vec![
        Kat {
            name: "empty-string",
            source: "NIST CAVP / FIPS 180-4 (canonical empty-input vector)",
            algo: "sha256",
            input: Value::Bytes(b"".to_vec()),
            expected: Value::bytes_hex(
                "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
            ),
        },
        Kat {
            name: "fips-180-4-B.1-abc",
            source: "FIPS 180-4 Appendix B.1",
            algo: "sha256",
            input: Value::Bytes(b"abc".to_vec()),
            expected: Value::bytes_hex(
                "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
            ),
        },
        Kat {
            name: "fips-180-4-B.2-448-bit-msg",
            source: "FIPS 180-4 Appendix B.2",
            algo: "sha256",
            input: Value::Bytes(
                b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq".to_vec(),
            ),
            expected: Value::bytes_hex(
                "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1",
            ),
        },
        // The three vectors above are the vendored KAT set; broader coverage
        // comes from the property-based test layer, with the Python oracle as
        // the reference.
    ]
}
