// Cryptographic algorithm instantiations. Each uses one or more
// composition patterns with concrete content (S-boxes, round constants,
// field parameters, curve points).
//
// The fifteen source modules are grouped by family:
//
//   hashes      — SHA-256, SHA-3-256, BLAKE3
//   symmetric   — AES-128 (ECB), ChaCha20, AES-128-CTR
//   aead        — AES-128-GCM, ChaCha20-Poly1305
//   mac         — HMAC-SHA-256, Poly1305
//   kdf         — HKDF-SHA-256, PBKDF2-HMAC-SHA-256
//   asymmetric  — RSA-PSS-SHA-256, Ed25519, X25519

pub mod aead;
pub mod asymmetric;
pub mod hashes;
pub mod kdf;
pub mod mac;
pub mod symmetric;
