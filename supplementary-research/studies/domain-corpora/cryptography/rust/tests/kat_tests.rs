//! Known-Answer Test entrypoint. Runs every vendored test vector
//! (FIPS / NIST SP / RFC / canonical-spec) against its composition and
//! asserts byte-exact equality.
//!
//! KATs are the strongest evidence in the cryptographic corpus —
//! the algorithm specification has authoritative ground truth, and a
//! composition that matches the vectors byte-for-byte demonstrates
//! the build works. This test runs only the vendored vectors; the
//! property-based layer (random byte inputs vs Python oracle) lives
//! in `corpus.rs`.

use dac_cryptography::config::{registry, CorpusEntry};
use dac_cryptography::equivalence::{equiv, Equiv};
use dac_cryptography::test_vectors;

fn entry_by_algo(name: &str) -> Option<CorpusEntry> {
    registry().into_iter().find(|e| e.oracle == name)
}

fn run_vectors<I: IntoIterator<Item = test_vectors::Kat>>(vectors: I) {
    let mut failures = Vec::new();
    for kat in vectors {
        let entry = entry_by_algo(kat.algo)
            .unwrap_or_else(|| panic!("KAT algorithm is absent from registry: {}", kat.algo));
        let got = (entry.compose)(kat.input.clone());
        if equiv(&got, &kat.expected, Equiv::Exact) {
            eprintln!("OK   {}/{}  ({})", kat.algo, kat.name, kat.source);
        } else {
            eprintln!(
                "FAIL {}/{}\n  source:   {}\n  input:    {:?}\n  got:      {:?}\n  expected: {:?}",
                kat.algo, kat.name, kat.source, kat.input, got, kat.expected
            );
            failures.push(format!("{}/{}", kat.algo, kat.name));
        }
    }
    assert!(failures.is_empty(), "KAT failures: {failures:?}");
}

#[test]
fn kat_sha256() {
    run_vectors(test_vectors::sha256::vectors());
}

#[test]
fn kat_sha3_256() {
    run_vectors(test_vectors::sha3_256::vectors());
}

#[test]
fn kat_blake3() {
    run_vectors(test_vectors::blake3::vectors());
}

#[test]
fn kat_chacha20() {
    run_vectors(test_vectors::chacha20::vectors());
}

#[test]
fn kat_hmac_sha256() {
    run_vectors(test_vectors::hmac_sha256::vectors());
}

#[test]
fn kat_hkdf_sha256() {
    run_vectors(test_vectors::hkdf_sha256::vectors());
}

#[test]
fn kat_pbkdf2_hmac_sha256() {
    run_vectors(test_vectors::pbkdf2::vectors());
}
