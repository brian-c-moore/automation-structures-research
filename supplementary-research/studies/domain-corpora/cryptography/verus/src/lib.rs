// Cryptography Verus crate — root module.
//
// Exploratory Verus cryptography sources. The tree contains extensive
// external-body trust boundaries, so it does not establish crate-wide
// algorithm correctness or implementation conformance. Each result is
// limited to its written contract and named trusted bodies.
//
// Crate layout:
//
//   content/        — cryptographic content (S-boxes, field arithmetic,
//                     curve parameters) vendored from the executable
//                     cryptography Rust crate with Verus annotations.
//   compositions/   — exploratory composition contracts with explicit
//                     uninterpreted and external-body boundaries.
//   algorithms/     — exploratory algorithm contracts with the same
//                     trust boundaries; no Rust-algorithm equivalence.
//   realizations/   — three implementation-realization patterns
//                     (bitsliced, hardware-accelerated, SIMD).
pub mod algorithms;
pub mod compositions;
pub mod constant_time;
pub mod modalities;
pub mod realizations;
