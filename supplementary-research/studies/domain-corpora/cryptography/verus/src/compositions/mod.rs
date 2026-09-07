// Cryptography composition patterns.
//
// Eleven composition patterns, each verified against the catalog
// primitives. The TLAPS structural specs at
// supplementary-research/studies/domain-corpora/cryptography/tla/compositions/
// (15 _Proof.tla modules, 3,576 obligations cold-deterministic) are the
// specification targets.
//
// iterated_transformation        — 12/15 algorithms; foundational
// tree_fold_of_chunks            — BLAKE3 parallel hashing
// absorb_then_squeeze            — SHA-3 sponge
// block_to_stream                — counter-mode keystream
// encrypt_then_authenticate      — AEAD (AES-GCM, ChaCha20-Poly1305)
// two_layer_wrap                 — HMAC
// polynomial_mac                 — Poly1305, GHASH (decomposed: horner/poly/equiv)
// scalar_multiplication          — RSA, Ed25519, X25519
// iteration_stretching           — PBKDF2
// extract_then_expand            — HKDF
// commit_challenge_response      — Ed25519 (decomposed: flow/distrib/verif)

pub mod absorb_then_squeeze;
pub mod block_to_stream;
pub mod commit_challenge_response;
pub mod encrypt_then_authenticate;
pub mod extract_then_expand;
pub mod iterated_transformation;
pub mod iteration_stretching;
pub mod polynomial_mac;
pub mod scalar_multiplication;
pub mod tree_fold_of_chunks;
pub mod two_layer_wrap;

// Classical algorithm composition patterns.
pub mod classical;
