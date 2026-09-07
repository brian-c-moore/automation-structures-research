//! Vendored official known-answer test (KAT) vectors.
//!
//! Per algorithm: input + expected output + a citation to the source
//! section (FIPS, NIST SP, RFC, or canonical specification document).
//! KATs are the strongest evidence — the algorithm specification has
//! authoritative ground truth, and a composition that matches the
//! vectors byte-for-byte demonstrates the build works.
//!
//! Each module vendors the vectors for one algorithm from its named
//! upstream standard or reference-vector set.

pub mod blake3;
pub mod chacha20;
pub mod hkdf_sha256;
pub mod hmac_sha256;
pub mod pbkdf2;
pub mod sha256;
pub mod sha3_256;

/// One known-answer test row.
#[derive(Debug, Clone)]
pub struct Kat {
    pub name: &'static str,
    /// Citation of the standard / section / vector ID.
    pub source: &'static str,
    /// Algorithm dispatch key (matches `CorpusEntry::oracle`).
    pub algo: &'static str,
    /// The input to the algorithm, in algorithm-specific shape.
    pub input: crate::value::Value,
    /// The expected output, byte-exact.
    pub expected: crate::value::Value,
}
