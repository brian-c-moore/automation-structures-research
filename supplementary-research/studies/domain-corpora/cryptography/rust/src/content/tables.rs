//! Fixed cryptographic tables: the content corpus algorithms consume.
//!
//! Each table is a `ResourceRegistry` instance (in framework terms),
//! filled at compile time and read during execution. The content is
//! reproduced from the algorithm's defining standard with a citation;
//! the tables are not derived in this module, math being content rather
//! than algorithm structure.
//!
//! Tables held here: SHA-256 round constants K[0..64] and initial hash
//! H[0..8].

// ---- SHA-256 (FIPS 180-4 §4.2.2 + §5.3.3) ------------------------------------

/// SHA-256 round constants K[0..64]. First 32 bits of the fractional
/// parts of the cube roots of the first 64 primes (FIPS 180-4 §4.2.2).
pub const SHA256_K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

/// SHA-256 initial hash H[0..8]. First 32 bits of the fractional parts
/// of the square roots of the first 8 primes (FIPS 180-4 §5.3.3).
pub const SHA256_H0: [u32; 8] = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

// ---- Keccak (SHA-3) (FIPS 202 §3.2 + §3.2.5) -----------------------------------

/// Keccak-f[1600] rotation offsets ρ[x, y], flat-indexed as `x + 5*y`.
/// All values are mod 64. (FIPS 202 §3.2.2, Table 2.)
pub const KECCAK_RHO: [u32; 25] = [
    // y = 0:   x=0  x=1  x=2  x=3  x=4
    0, 1, 62, 28, 27, // y = 1:
    36, 44, 6, 55, 20, // y = 2:
    3, 10, 43, 25, 39, // y = 3:
    41, 45, 15, 21, 8, // y = 4:
    18, 2, 61, 56, 14,
];

/// Keccak-f[1600] round constants RC[0..24] (FIPS 202 §3.2.5, Table 1).
/// Derived from the LFSR over GF(2)/(x^8 + x^6 + x^5 + x^4 + 1); the
/// values are reproduced here verbatim from the standard.
pub const KECCAK_RC: [u64; 24] = [
    0x0000000000000001,
    0x0000000000008082,
    0x800000000000808a,
    0x8000000080008000,
    0x000000000000808b,
    0x0000000080000001,
    0x8000000080008081,
    0x8000000000008009,
    0x000000000000008a,
    0x0000000000000088,
    0x0000000080008009,
    0x000000008000000a,
    0x000000008000808b,
    0x800000000000008b,
    0x8000000000008089,
    0x8000000000008003,
    0x8000000000008002,
    0x8000000000000080,
    0x000000000000800a,
    0x800000008000000a,
    0x8000000080008081,
    0x8000000000008080,
    0x0000000080000001,
    0x8000000080008008,
];

// ---- BLAKE3 (BLAKE3 spec §2.1, §2.2) -------------------------------------------

/// BLAKE3 initial chaining value (the same eight constants as BLAKE2s
/// and SHA-256: first 32 bits of the fractional parts of √2, √3, √5, √7,
/// √11, √13, √17, √19). Equal to [`SHA256_H0`] but kept as a separate
/// constant so the algorithm spec is self-contained.
pub const BLAKE3_IV: [u32; 8] = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

/// BLAKE3 message permutation σ applied between rounds in the
/// compression function (BLAKE3 spec §2.1.2).
pub const BLAKE3_MSG_PERMUTATION: [usize; 16] =
    [2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8];

// BLAKE3 domain-separation flags (BLAKE3 spec §2.1).
pub const BLAKE3_FLAG_CHUNK_START: u32 = 1 << 0;
pub const BLAKE3_FLAG_CHUNK_END: u32 = 1 << 1;
pub const BLAKE3_FLAG_PARENT: u32 = 1 << 2;
pub const BLAKE3_FLAG_ROOT: u32 = 1 << 3;
pub const BLAKE3_FLAG_KEYED_HASH: u32 = 1 << 4;
pub const BLAKE3_FLAG_DERIVE_KEY_CONTEXT: u32 = 1 << 5;
pub const BLAKE3_FLAG_DERIVE_KEY_MATERIAL: u32 = 1 << 6;
