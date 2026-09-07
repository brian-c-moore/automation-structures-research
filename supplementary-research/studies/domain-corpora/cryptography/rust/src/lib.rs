//! # Cryptography executable subset
//!
//! Seven algorithms exercise six primitives
//! ([`primitives::ResourceRegistry`], [`primitives::TraversalEngine`],
//! [`primitives::ActuationPass`], [`primitives::Reduction`],
//! [`primitives::Bisection`], [`primitives::Sampler`]) plus whatever
//! content each algorithm consumes. The executable subset contains
//! SHA-256, SHA-3-256, BLAKE3, ChaCha20, HMAC-SHA-256, HKDF-SHA-256,
//! and PBKDF2-HMAC-SHA-256. It makes no claim about algorithms outside
//! that exact list.
//!
//! ## Layout (mirrors `supplementary-research/studies/domain-corpora/algorithms/rust/`)
//!
//! - [`primitive`]   - the `AbstractionPrimitive` trait.
//! - [`primitives`]  - six reusable mechanisms, each in its own file.
//! - [`content`]     - cryptographic content the operations consume:
//!   byte strings, finite-field arithmetic, S-boxes, round constants,
//!   curve arithmetic, and bignum limbs.
//! - [`compositions`] - the exact seven-algorithm subset across hashes,
//!   symmetric stream encryption, MAC, and KDF families. Every
//!   composition is built only from [`primitives`] and [`content`], with
//!   no direct cryptographic-library calls.
//! - [`test_vectors`] - vendored official KAT vectors (FIPS, NIST SP,
//!   RFC, canonical specs).
//! - [`equivalence`] - byte-exact comparison.
//! - [`oracle`]      - bridge to the exact Python references.
//! - [`config`]      - in-process algorithm registry.
//! - [`harness`]     - input generation, dual run, and comparison.
//!
//! ## Cross-corpus framing
//!
//! Five of the six primitives ([`primitives::ResourceRegistry`],
//! [`primitives::TraversalEngine`], [`primitives::ActuationPass`],
//! [`primitives::Reduction`], [`primitives::Bisection`]) are shared with
//! the 87-algorithm classical corpus at `supplementary-research/studies/domain-corpora/algorithms/rust/`.
//! [`primitives::Sampler`] is asymmetric: cryptography needs it (entropy
//! reads, rejection sampling, witness generation, RSA-PSS salts) and the
//! executable classical-corpus uses do not.

pub mod compositions;
pub mod config;
pub mod content;
pub mod equivalence;
pub mod harness;
pub mod oracle;
pub mod primitive;
pub mod primitives;
pub mod test_vectors;
pub mod value;

pub use primitive::AbstractionPrimitive;
pub use value::Value;
