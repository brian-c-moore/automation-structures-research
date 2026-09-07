//! Message authentication: HMAC-SHA-256.
//!
//! HMAC instantiates the two-layer-wrap pattern over SHA-256: the hash
//! transformation is applied twice in sequence with key-derived prefixes
//! (`K XOR ipad`, `K XOR opad`).

use super::entry;
use crate::compositions::hashes::sha256;
use crate::config::CorpusEntry;
use crate::content::byte_string::xor_into;
use crate::equivalence::Equiv;
use crate::primitives::Sampler;
use crate::value::Value;

// =====================================================================
// HMAC-SHA-256 — RFC 2104, RFC 4231
// =====================================================================
//
// Composition shape:
//   ResourceRegistry over the key, the ipad/opad constants (implicit as
//     byte constants 0x36 and 0x5C), and the intermediate digest.
//   ActuationPass for the XOR-with-pad steps (preparing the inner and
//     outer hash inputs).
//   Reduction (XOR) at the per-byte level inside the pad operations.
//   The two SHA-256 invocations are vendored from compositions::hashes,
//     which is itself the iterated-transformation-over-chained-state
//     composition.
//
// Structural ordering: Linear (outer hash depends on inner hash).
// Modality: Sequential.

const SHA256_BLOCK: usize = 64;

const IPAD: u8 = 0x36;
const OPAD: u8 = 0x5C;

/// HMAC-SHA-256, built only from primitives + content + the
/// SHA-256 composition.
pub fn hmac_sha256(key: &[u8], message: &[u8]) -> [u8; 32] {
    // Step 1: normalize key to block-size (64 bytes). If too long, hash
    // it. (RFC 2104 §2; reuses sha256 verbatim.)
    let mut key_block = [0u8; SHA256_BLOCK];
    if key.len() > SHA256_BLOCK {
        let h = sha256(key);
        key_block[..32].copy_from_slice(&h);
    } else {
        key_block[..key.len()].copy_from_slice(key);
    }

    // Step 2: build inner and outer prefixes via XOR-Reduction with the
    // ipad/opad constants. ActuationPass per-block.
    let mut inner_key = [IPAD; SHA256_BLOCK];
    xor_into(&mut inner_key, &key_block);
    let mut outer_key = [OPAD; SHA256_BLOCK];
    xor_into(&mut outer_key, &key_block);

    // Step 3: inner hash = SHA-256(inner_key || message).
    let mut inner_input = Vec::with_capacity(SHA256_BLOCK + message.len());
    inner_input.extend_from_slice(&inner_key);
    inner_input.extend_from_slice(message);
    let inner_digest = sha256(&inner_input);

    // Step 4: outer hash = SHA-256(outer_key || inner_digest).
    let mut outer_input = Vec::with_capacity(SHA256_BLOCK + 32);
    outer_input.extend_from_slice(&outer_key);
    outer_input.extend_from_slice(&inner_digest);
    sha256(&outer_input)
}

// ---- Harness adapter ---------------------------------------------------------
//
// Input shape (Value::List):
//   [ Bytes(key), Bytes(message) ]
// Output shape:
//   Bytes(tag:32)

fn hmac_sha256_compose(input: Value) -> Value {
    let parts = input.as_list();
    let key = parts[0].as_bytes();
    let message = parts[1].as_bytes();
    Value::Bytes(hmac_sha256(&key, &message).to_vec())
}

fn hmac_sha256_inputs() -> Vec<Value> {
    let mut s = Sampler::new(0xABBA1234);
    let mut out = Vec::with_capacity(40);

    // Curated edge cases on key length:
    //   - empty key
    //   - 1 byte
    //   - 63 bytes (one byte short of block)
    //   - 64 bytes (exactly block)
    //   - 65 bytes (overflows, no hashing yet)
    //   - 100 bytes (will be hashed down to 32)
    for klen in [0usize, 1, 63, 64, 65, 100] {
        for mlen in [0usize, 1, 63, 64, 65] {
            out.push(Value::List(vec![
                Value::Bytes(s.bytes(klen)),
                Value::Bytes(s.bytes(mlen)),
            ]));
        }
    }

    // Random tuples for broader coverage.
    for _ in 0..16 {
        let klen = s.pick_index(200);
        let mlen = s.pick_index(257);
        out.push(Value::List(vec![
            Value::Bytes(s.bytes(klen)),
            Value::Bytes(s.bytes(mlen)),
        ]));
    }

    out
}

// ---- Registry ----------------------------------------------------------------

pub fn add(r: &mut Vec<CorpusEntry>) {
    entry(
        r,
        "hmac_sha256",
        "mac",
        4,
        "Linear",
        "SHA-256 (composed twice) + Reduction (XOR) over ipad/opad prefixes",
        hmac_sha256_compose,
        "hmac_sha256",
        Equiv::Exact,
        hmac_sha256_inputs,
    );

}

// ---- Unit tests against the canonical RFC 4231 vectors -------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::hex_encode;

    /// RFC 4231 §4.2 Test 1: 20-byte 0x0b key, "Hi There".
    #[test]
    fn hmac_rfc4231_test_1() {
        let key = [0x0bu8; 20];
        let msg = b"Hi There";
        let got = hmac_sha256(&key, msg);
        assert_eq!(
            hex_encode(&got),
            "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7"
        );
    }

    /// RFC 4231 §4.3 Test 2: "Jefe" key, "what do ya want for nothing?".
    #[test]
    fn hmac_rfc4231_test_2() {
        let got = hmac_sha256(b"Jefe", b"what do ya want for nothing?");
        assert_eq!(
            hex_encode(&got),
            "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843"
        );
    }

    /// RFC 4231 §4.4 Test 3: 20-byte 0xaa key, 50-byte 0xdd message.
    #[test]
    fn hmac_rfc4231_test_3() {
        let key = [0xaau8; 20];
        let msg = [0xddu8; 50];
        let got = hmac_sha256(&key, &msg);
        assert_eq!(
            hex_encode(&got),
            "773ea91e36800e46854db8ebd09181a72959098b3ef8c122d9635514ced565fe"
        );
    }

    /// RFC 4231 §4.6 Test 5 (truncation): key=[0x0c]×20, msg="Test With Truncation".
    /// The HMAC-SHA-256 output is shown in full; truncation is the
    /// caller's responsibility.
    #[test]
    fn hmac_rfc4231_test_5() {
        let key = [0x0cu8; 20];
        let msg = b"Test With Truncation";
        let got = hmac_sha256(&key, msg);
        assert_eq!(
            hex_encode(&got),
            "a3b6167473100ee06e0c796c2955552bfa6f7c0a6a8aef8b93f860aab0cd20c5"
        );
    }
}
