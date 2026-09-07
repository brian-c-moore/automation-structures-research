//! Key-derivation functions: HKDF-SHA-256 and PBKDF2-HMAC-SHA-256.
//!
//! HKDF instantiates the extract-then-expand pattern:
//! two phases, where the extract phase compresses possibly-non-uniform
//! input keying material into a uniform PRK via a single HMAC
//! invocation, and the expand phase produces arbitrary-length output
//! by iteratively applying HMAC under the PRK with a counter.

use super::entry;
use crate::compositions::mac::hmac_sha256;
use crate::config::CorpusEntry;
use crate::equivalence::Equiv;
use crate::primitives::Sampler;
use crate::value::Value;

// =====================================================================
// HKDF-SHA-256 — RFC 5869
// =====================================================================
//
// Composition shape:
//   Phase 1 (extract): single HMAC-SHA-256 invocation, PRK = HMAC(salt, IKM).
//   Phase 2 (expand): TraversalEngine over the output blocks; each block
//     T_i = HMAC(PRK, T_{i-1} || info || i). The concatenation of
//     T_1 || T_2 || ... is truncated to the requested length.
//
// Structural ordering: Linear within expand (each T_i depends on
// T_{i-1}). Modality: Sequential.

const HASH_LEN: usize = 32; // SHA-256 output length

/// HKDF Extract (RFC 5869 §2.2). Compresses (salt, IKM) into a 32-byte
/// PRK via one HMAC-SHA-256 call. Empty salt defaults to 32 zero bytes
/// per RFC 5869 §2.2.
fn hkdf_extract(salt: &[u8], ikm: &[u8]) -> [u8; 32] {
    let salt_buf: Vec<u8>;
    let salt_slice: &[u8] = if salt.is_empty() {
        salt_buf = vec![0u8; HASH_LEN];
        &salt_buf
    } else {
        salt
    };
    hmac_sha256(salt_slice, ikm)
}

/// HKDF Expand (RFC 5869 §2.3). Produces `length` bytes of OKM from
/// the PRK and info. `length` must be at most 255 × HASH_LEN
/// (= 8160 bytes for SHA-256). The TraversalEngine here walks the
/// counter `i` from 1 to ceil(length / HASH_LEN); each step is an
/// HMAC invocation whose input is the previous block, the info, and
/// the counter byte.
fn hkdf_expand(prk: &[u8; 32], info: &[u8], length: usize) -> Vec<u8> {
    assert!(
        length <= 255 * HASH_LEN,
        "HKDF Expand: length exceeds 255 * HashLen"
    );

    let n_blocks = (length + HASH_LEN - 1) / HASH_LEN;
    let mut okm = Vec::with_capacity(n_blocks * HASH_LEN);
    let mut t_prev: Vec<u8> = Vec::new();

    for i in 1..=n_blocks {
        let mut input = Vec::with_capacity(t_prev.len() + info.len() + 1);
        input.extend_from_slice(&t_prev);
        input.extend_from_slice(info);
        input.push(i as u8); // counter byte (i fits in u8 because n_blocks <= 255)
        let t_i = hmac_sha256(prk, &input);
        okm.extend_from_slice(&t_i);
        t_prev = t_i.to_vec();
    }
    okm.truncate(length);
    okm
}

/// HKDF-SHA-256 composing Extract + Expand (RFC 5869 §2.1).
pub fn hkdf_sha256(salt: &[u8], ikm: &[u8], info: &[u8], length: usize) -> Vec<u8> {
    let prk = hkdf_extract(salt, ikm);
    hkdf_expand(&prk, info, length)
}

// ---- Harness adapter ---------------------------------------------------------
//
// Input shape (Value::List):
//   [ Bytes(salt), Bytes(ikm), Bytes(info), Int(length) ]
// Output shape:
//   Bytes(OKM)

fn hkdf_sha256_compose(input: Value) -> Value {
    let parts = input.as_list();
    let salt = parts[0].as_bytes();
    let ikm = parts[1].as_bytes();
    let info = parts[2].as_bytes();
    let length = parts[3].as_int() as usize;
    Value::Bytes(hkdf_sha256(&salt, &ikm, &info, length))
}

fn hkdf_sha256_inputs() -> Vec<Value> {
    let mut s = Sampler::new(0xFACE2);
    let mut out = Vec::with_capacity(40);

    // Curated edge cases.
    for length in [1usize, 31, 32, 33, 64, 96, 200] {
        out.push(Value::List(vec![
            Value::Bytes(s.bytes(13)), // typical salt length
            Value::Bytes(s.bytes(22)), // typical IKM length
            Value::Bytes(s.bytes(10)), // typical info length
            Value::Int(length as i64),
        ]));
    }
    // Empty salt edge case.
    out.push(Value::List(vec![
        Value::Bytes(Vec::new()),
        Value::Bytes(s.bytes(22)),
        Value::Bytes(Vec::new()),
        Value::Int(42),
    ]));

    // Random tuples.
    for _ in 0..16 {
        let saltlen = s.pick_index(64);
        let ikmlen = 1 + s.pick_index(80); // IKM should be non-empty
        let infolen = s.pick_index(64);
        let length = 1 + s.pick_index(200);
        out.push(Value::List(vec![
            Value::Bytes(s.bytes(saltlen)),
            Value::Bytes(s.bytes(ikmlen)),
            Value::Bytes(s.bytes(infolen)),
            Value::Int(length as i64),
        ]));
    }

    out
}

// =====================================================================
// PBKDF2-HMAC-SHA-256 — RFC 2898
// =====================================================================
//
// Composition shape (iteration stretching):
//   For each output block i in 1..=ceil(L/HashLen):
//     U_1 = HMAC(P, S || INT(i))
//     U_j = HMAC(P, U_{j-1}) for j in 2..=c
//     T_i = U_1 XOR U_2 XOR ... XOR U_c   (Reduction over the chain)
//   DK = T_1 || T_2 || ... truncated to L bytes
//
// Structural ordering: Linear within each block (each U_j depends on
// U_{j-1}). Modality: Sequential within a block (the chain cannot be
// parallelized — that is the cryptographic purpose); Fork-join
// admissible across output blocks (different output-block counters
// produce independent chains).

/// PBKDF2-HMAC-SHA-256 (RFC 2898 §5.2). `iterations` is the chain
/// length c (the iteration-stretching parameter).
pub fn pbkdf2_hmac_sha256(password: &[u8], salt: &[u8], iterations: u32, length: usize) -> Vec<u8> {
    assert!(iterations >= 1, "PBKDF2 iterations must be >= 1");

    let mut dk = Vec::with_capacity(length);
    let block_count = (length + HASH_LEN - 1) / HASH_LEN;

    // TraversalEngine over output blocks (Tree at this level — each
    // block is independent given the counter).
    for i in 1..=block_count {
        // U_1 = HMAC(password, salt || INT(i)).
        let mut salt_i = Vec::with_capacity(salt.len() + 4);
        salt_i.extend_from_slice(salt);
        salt_i.extend_from_slice(&(i as u32).to_be_bytes());
        let mut u = hmac_sha256(password, &salt_i);

        // T_i = U_1 XOR U_2 XOR ... XOR U_c. Reduction over the U chain.
        let mut t_i = u;

        // TraversalEngine over the iteration chain (Linear within block —
        // the U_j chain cannot be parallelized; this is the
        // iteration-stretching defence).
        for _ in 1..iterations {
            u = hmac_sha256(password, &u);
            for k in 0..HASH_LEN {
                t_i[k] ^= u[k];
            }
        }
        dk.extend_from_slice(&t_i);
    }
    dk.truncate(length);
    dk
}

fn pbkdf2_hmac_sha256_compose(input: Value) -> Value {
    let parts = input.as_list();
    let password = parts[0].as_bytes();
    let salt = parts[1].as_bytes();
    let iterations = parts[2].as_int() as u32;
    let length = parts[3].as_int() as usize;
    Value::Bytes(pbkdf2_hmac_sha256(&password, &salt, iterations, length))
}

/// Property-based inputs for PBKDF2: iteration counts are kept small so
/// the test suite stays fast. The 80000-iteration RFC 7914 vector is
/// covered separately as a known-answer test.
fn pbkdf2_hmac_sha256_inputs() -> Vec<Value> {
    let mut s = Sampler::new(0xDEFADAF);
    let mut out = Vec::with_capacity(24);

    // Curated edge cases with iterations in {1, 2, 5}.
    for &iters in &[1u32, 2, 5] {
        for length in [1usize, 31, 32, 33, 64, 96] {
            out.push(Value::List(vec![
                Value::Bytes(s.bytes(16)),
                Value::Bytes(s.bytes(16)),
                Value::Int(iters as i64),
                Value::Int(length as i64),
            ]));
        }
    }

    out
}

// ---- Registry ----------------------------------------------------------------

pub fn add(r: &mut Vec<CorpusEntry>) {
    entry(
        r,
        "hkdf_sha256",
        "kdf",
        5,
        "Tree (extract|expand are sequential phases), Linear (within expand chain)",
        "HMAC-SHA-256 composed once (extract) + TraversalEngine over expand blocks",
        hkdf_sha256_compose,
        "hkdf_sha256",
        Equiv::Exact,
        hkdf_sha256_inputs,
    );
    entry(
        r,
        "pbkdf2_hmac_sha256",
        "kdf",
        5,
        "Tree (output blocks), Linear (within-block U-chain)",
        "HMAC-SHA-256 chained c times + Reduction (XOR over U_1..U_c)",
        pbkdf2_hmac_sha256_compose,
        "pbkdf2_hmac_sha256",
        Equiv::Exact,
        pbkdf2_hmac_sha256_inputs,
    );
}

// ---- Unit tests against the canonical RFC 5869 vectors ---------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::hex_encode;

    /// RFC 5869 Appendix A.1: Basic test case with SHA-256.
    #[test]
    fn hkdf_rfc5869_a_1() {
        let ikm = [0x0bu8; 22];
        let salt = [
            0x00u8, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c,
        ];
        let info = [0xf0u8, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8, 0xf9];
        let okm = hkdf_sha256(&salt, &ikm, &info, 42);
        assert_eq!(
            hex_encode(&okm),
            "3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf34007208d5b887185865"
        );
    }

    /// RFC 5869 Appendix A.3: Test with zero-length salt and info.
    #[test]
    fn hkdf_rfc5869_a_3() {
        let ikm = [0x0bu8; 22];
        let okm = hkdf_sha256(&[], &ikm, &[], 42);
        assert_eq!(
            hex_encode(&okm),
            "8da4e775a563c18f715f802a063c5a31b8a11f5c5ee1879ec3454e5f3c738d2d9d201395faa4b61a96c8"
        );
    }

    // ---- PBKDF2-HMAC-SHA-256 KAT vectors ----

    /// RFC 7914 §11 PBKDF2-HMAC-SHA-256 vector with c=1, dkLen=64.
    #[test]
    fn pbkdf2_rfc7914_passwd_salt_c1() {
        let got = pbkdf2_hmac_sha256(b"passwd", b"salt", 1, 64);
        assert_eq!(
            hex_encode(&got),
            "55ac046e56e3089fec1691c22544b605f94185216dde0465e68b9d57c20dacbc49ca9cccf179b645991664b39d77ef317c71b845b1e30bd509112041d3a19783"
        );
    }
}
