//! ChaCha20 symmetric-stream construction.
//!
//! ChaCha20 instantiates the iterated-transformation-over-chained-state
//! pattern with an ARX round function, plus the
//! block-to-stream conversion pattern that wraps the
//! block transformation with a counter-driven `TraversalEngine` to
//! produce arbitrary-length keystream.

use super::entry;
use crate::config::CorpusEntry;
use crate::content::byte_string::{le_u32, le_u32_to_bytes, xor_into};
use crate::equivalence::Equiv;
use crate::primitives::{Reduction, Sampler, TraversalEngine};
use crate::value::Value;

// =====================================================================
// ChaCha20 — RFC 8439
// =====================================================================
//
// Composition shape:
//   ResourceRegistry over the 16 state words and the keystream blocks.
//   TraversalEngine over the 20 rounds, the four quarter-round groups
//     within each double-round, and the input blocks (counter-driven).
//   ActuationPass per quarter round.
//   Reduction (mod-2^32 addition for the final state add; XOR for
//     applying the keystream to plaintext).
//
// Structural ordering: Tree at the block level (counter-driven, each
// block's keystream depends only on counter and key); Linear within
// each block at the double-round level. Modality: Sequential within a
// block as taught; Fork-join admissible across blocks.

/// The four ChaCha20 "expand 32-byte k" constants (RFC 8439 §2.3).
const CHACHA20_CONSTANTS: [u32; 4] = [0x61707865, 0x3320646E, 0x79622D32, 0x6B206574];

/// ChaCha20 quarter-round: ARX on four state words a, b, c, d.
/// (RFC 8439 §2.1.)
#[inline]
fn quarter_round(state: &mut [u32; 16], a: usize, b: usize, c: usize, d: usize) {
    state[a] = state[a].wrapping_add(state[b]);
    state[d] = (state[d] ^ state[a]).rotate_left(16);
    state[c] = state[c].wrapping_add(state[d]);
    state[b] = (state[b] ^ state[c]).rotate_left(12);
    state[a] = state[a].wrapping_add(state[b]);
    state[d] = (state[d] ^ state[a]).rotate_left(8);
    state[c] = state[c].wrapping_add(state[d]);
    state[b] = (state[b] ^ state[c]).rotate_left(7);
}

/// One ChaCha20 double-round = 4 column quarter-rounds + 4 diagonal
/// quarter-rounds (RFC 8439 §2.3). 10 double-rounds = 20 rounds total.
fn double_round(state: &mut [u32; 16]) {
    // 4 columns
    quarter_round(state, 0, 4, 8, 12);
    quarter_round(state, 1, 5, 9, 13);
    quarter_round(state, 2, 6, 10, 14);
    quarter_round(state, 3, 7, 11, 15);
    // 4 diagonals
    quarter_round(state, 0, 5, 10, 15);
    quarter_round(state, 1, 6, 11, 12);
    quarter_round(state, 2, 7, 8, 13);
    quarter_round(state, 3, 4, 9, 14);
}

/// ChaCha20 block function (RFC 8439 §2.3). Produces a 64-byte
/// keystream block from `(key, counter, nonce)`. Built only from
/// primitives + content.
pub fn chacha20_block(key: &[u8; 32], counter: u32, nonce: &[u8; 12]) -> [u8; 64] {
    // ResourceRegistry: the 16-word initial state.
    //   words 0..3  = constants
    //   words 4..11 = key (8 little-endian words)
    //   word  12    = block counter
    //   words 13..15 = nonce (3 little-endian words)
    let mut initial = [0u32; 16];
    initial[0..4].copy_from_slice(&CHACHA20_CONSTANTS);
    for i in 0..8 {
        initial[4 + i] = le_u32(key, i * 4);
    }
    initial[12] = counter;
    for i in 0..3 {
        initial[13 + i] = le_u32(nonce, i * 4);
    }

    let mut working = initial;

    // TraversalEngine over the 10 double-rounds (= 20 rounds).
    TraversalEngine::iter_rounds(&mut working, 10, |state, _i| {
        double_round(state);
    });

    // Final state add: Reduction (mod-2^32) of working state + initial state.
    let mut out_words = [0u32; 16];
    for i in 0..16 {
        out_words[i] =
            Reduction::reduce(vec![working[i], initial[i]], 0u32, |x, y| x.wrapping_add(y));
    }

    // Serialize as 64 little-endian bytes.
    let mut out = [0u8; 64];
    for i in 0..16 {
        out[i * 4..i * 4 + 4].copy_from_slice(&le_u32_to_bytes(out_words[i]));
    }
    out
}

/// ChaCha20 encrypt/decrypt (RFC 8439 §2.4): block-to-stream conversion
/// over [`chacha20_block`]. XOR each keystream block into the
/// corresponding plaintext block; the final partial block is truncated
/// to the plaintext's length.
pub fn chacha20_encrypt(
    key: &[u8; 32],
    initial_counter: u32,
    nonce: &[u8; 12],
    plaintext: &[u8],
) -> Vec<u8> {
    let mut out = vec![0u8; plaintext.len()];
    // ResourceRegistry tracks "next byte to encrypt"; TraversalEngine
    // walks 64-byte input chunks (Tree-shaped at the block level —
    // counter-driven by design).
    let block_count = (plaintext.len() + 63) / 64;
    for b in 0..block_count {
        let counter = initial_counter.wrapping_add(b as u32);
        let ks = chacha20_block(key, counter, nonce);
        let off = b * 64;
        let end = (off + 64).min(plaintext.len());
        out[off..end].copy_from_slice(&plaintext[off..end]);
        // Reduction (XOR) of keystream into plaintext bytes.
        xor_into(&mut out[off..end], &ks[..end - off]);
    }
    out
}

// ---- Harness adapters --------------------------------------------------------
//
// Input shape (Value::List):
//   [ Bytes(key:32),  Bytes(nonce:12),  Int(counter),  Bytes(plaintext) ]
// Output shape:
//   Bytes(ciphertext)  (same length as plaintext)

fn chacha20_compose(input: Value) -> Value {
    let parts = input.as_list();
    let key_vec = parts[0].as_bytes();
    let nonce_vec = parts[1].as_bytes();
    let counter = parts[2].as_int() as u32;
    let plaintext = parts[3].as_bytes();

    let mut key = [0u8; 32];
    key.copy_from_slice(&key_vec);
    let mut nonce = [0u8; 12];
    nonce.copy_from_slice(&nonce_vec);

    Value::Bytes(chacha20_encrypt(&key, counter, &nonce, &plaintext))
}

/// Property-based inputs for ChaCha20: random (key, nonce, counter,
/// plaintext) tuples with plaintext lengths spanning block boundaries.
fn chacha20_inputs() -> Vec<Value> {
    let mut s = Sampler::new(0xCAFEBABE);
    let mut out = Vec::with_capacity(40);

    // Curated edge cases: plaintext lengths around block boundaries.
    for plen in [0usize, 1, 63, 64, 65, 127, 128, 129] {
        out.push(Value::List(vec![
            Value::Bytes(s.bytes(32)),
            Value::Bytes(s.bytes(12)),
            Value::Int((s.pick_index(1024)) as i64),
            Value::Bytes(s.bytes(plen)),
        ]));
    }

    // Random plaintext lengths up to 256 bytes.
    for _ in 0..32 {
        let plen = s.pick_index(257);
        out.push(Value::List(vec![
            Value::Bytes(s.bytes(32)),
            Value::Bytes(s.bytes(12)),
            Value::Int((s.pick_index(1024)) as i64),
            Value::Bytes(s.bytes(plen)),
        ]));
    }

    out
}

// ---- Registry ----------------------------------------------------------------

pub fn add(r: &mut Vec<CorpusEntry>) {
    entry(
        r,
        "chacha20",
        "symmetric",
        2,
        "Tree (blocks), Linear (within block)",
        "ResourceRegistry + TraversalEngine + ActuationPass + Reduction (mod-2^32 add, XOR)",
        chacha20_compose,
        "chacha20",
        Equiv::Exact,
        chacha20_inputs,
    );
}

// ---- Unit tests against the canonical RFC 8439 vector --------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::hex_encode;

    /// RFC 8439 §2.3.2 keystream block:
    /// key = 0001020304..1F, nonce = 000000090000004A00000000, counter = 1.
    /// First 64 bytes of keystream match the published test vector.
    #[test]
    fn chacha20_block_rfc8439_section_2_3_2() {
        let mut key = [0u8; 32];
        for i in 0..32 {
            key[i] = i as u8;
        }
        let mut nonce = [0u8; 12];
        nonce[3] = 0x09;
        nonce[7] = 0x4a;
        let counter = 1u32;

        let block = chacha20_block(&key, counter, &nonce);
        assert_eq!(
            hex_encode(&block),
            "10f1e7e4d13b5915500fdd1fa32071c4c7d1f4c733c068030422aa9ac3d46c4ed2826446079faa0914c2d705d98b02a2b5129cd1de164eb9cbd083e8a2503c4e"
        );
    }

    /// RFC 8439 §2.4.2 encryption: encrypt the 114-byte "Ladies and
    /// Gentlemen..." plaintext with counter=1 and the same key/nonce
    /// as §2.3.2 (modified: nonce is 000000000000004a00000000).
    #[test]
    fn chacha20_encrypt_rfc8439_section_2_4_2() {
        let mut key = [0u8; 32];
        for i in 0..32 {
            key[i] = i as u8;
        }
        let mut nonce = [0u8; 12];
        nonce[7] = 0x4a;
        let counter = 1u32;

        let plaintext = b"Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it.";
        let got = chacha20_encrypt(&key, counter, &nonce, plaintext);
        assert_eq!(
            hex_encode(&got),
            "6e2e359a2568f98041ba0728dd0d6981e97e7aec1d4360c20a27afccfd9fae0bf91b65c5524733ab8f593dabcd62b3571639d624e65152ab8f530c359f0861d807ca0dbf500d6a6156a38e088a22b65e52bc514d16ccf806818ce91ab77937365af90bbf74a35be6b40b8eedf2785e42874d"
        );
    }
}
