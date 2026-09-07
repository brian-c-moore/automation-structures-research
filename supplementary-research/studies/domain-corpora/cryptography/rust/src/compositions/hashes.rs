//! Hashes.
//!
//! Every algorithm here is the **iterated-transformation-over-chained-state
//! composition**, instantiated with the
//! algorithm's specific round function and content:
//!
//! - SHA-256: 64 compression rounds per 512-bit block (§2).
//! - SHA-3-256: 24 permutation rounds per absorb step, sponge
//!   construction with 1088-bit rate (§3).
//! - BLAKE3: 7-round G-function compressions composed up a binary tree
//!   via the tree-fold-of-chunks pattern.
//!
//! All three reuse the shared primitive and content modules.
//! Structural ordering: **Linear** (SHA-256, SHA-3) at the algorithm
//! level. **Tree** at the chunk level (BLAKE3); Linear within each
//! chunk compression.
//!
//! TLA+ structural-correctness counterparts:
//!   `supplementary-research/studies/domain-corpora/cryptography/tla/compositions/IteratedTransformationOverChainedState.tla`
//!   `supplementary-research/studies/domain-corpora/cryptography/tla/compositions/TreeFoldOfChunks.tla`
//!   `supplementary-research/studies/domain-corpora/cryptography/tla/compositions/AbsorbThenSqueeze.tla`

use super::{entry, gen};
use crate::config::CorpusEntry;
use crate::content::byte_string::{be_u32, be_u32_to_bytes, pad_md};
use crate::content::keccak::keccak_f1600;
use crate::content::tables::{
    BLAKE3_FLAG_CHUNK_END, BLAKE3_FLAG_CHUNK_START, BLAKE3_FLAG_PARENT, BLAKE3_FLAG_ROOT,
    BLAKE3_IV, BLAKE3_MSG_PERMUTATION, SHA256_H0, SHA256_K,
};
use crate::equivalence::Equiv;
use crate::primitives::{Reduction, ResourceRegistry, TraversalEngine};
use crate::value::Value;

// =====================================================================
// SHA-256
// =====================================================================
//
// Composition shape:
//   ResourceRegistry over the eight state words, sixty-four
//     message-schedule words, and sixty-four round constants.
//   TraversalEngine over input blocks, schedule positions 16..63,
//     and the sixty-four compression rounds.
//   ActuationPass per round (the state update).
//   Reduction (mod-2^32 addition) at multiple points internally.
//
// Structural ordering: Linear. Each compression round depends on the
// prior round's state; each schedule word at i (i >= 16) depends on
// positions i-2, i-7, i-15, i-16; each block's final state-add
// depends on the compression output of that block. Modality:
// Sequential within an invocation; Fork-join admissible across
// independent messages.

const SHA256_BLOCK: usize = 64; // 512 bits

// SHA-256's six bitwise mixing functions (FIPS 180-4 §4.1.2).
#[inline]
fn rotr(x: u32, n: u32) -> u32 {
    x.rotate_right(n)
}
#[inline]
fn ch(x: u32, y: u32, z: u32) -> u32 {
    (x & y) ^ (!x & z)
}
#[inline]
fn maj(x: u32, y: u32, z: u32) -> u32 {
    (x & y) ^ (x & z) ^ (y & z)
}
#[inline]
fn big_sigma0(x: u32) -> u32 {
    rotr(x, 2) ^ rotr(x, 13) ^ rotr(x, 22)
}
#[inline]
fn big_sigma1(x: u32) -> u32 {
    rotr(x, 6) ^ rotr(x, 11) ^ rotr(x, 25)
}
#[inline]
fn small_sigma0(x: u32) -> u32 {
    rotr(x, 7) ^ rotr(x, 18) ^ (x >> 3)
}
#[inline]
fn small_sigma1(x: u32) -> u32 {
    rotr(x, 17) ^ rotr(x, 19) ^ (x >> 10)
}

/// SHA-256, built only from primitives + content.
pub fn sha256(msg: &[u8]) -> [u8; 32] {
    // ResourceRegistry: the 8 working state words, keyed by position.
    let mut state: ResourceRegistry<usize, u32> = ResourceRegistry::new();
    for (i, &h) in SHA256_H0.iter().enumerate() {
        state.insert(i, h);
    }

    let padded = pad_md(msg, SHA256_BLOCK);

    // TraversalEngine over the input blocks.
    let blocks = padded.len() / SHA256_BLOCK;
    TraversalEngine::iter_rounds(&mut state, blocks, |state, b| {
        let off = b * SHA256_BLOCK;

        // ResourceRegistry: the 64-word message schedule W[0..64].
        // (Held as a stack array for arithmetic speed; the registry
        // semantics are the same — unique value per position.)
        let mut w = [0u32; 64];

        // First 16 words: load big-endian from the block (TraversalEngine
        // over schedule positions 0..15).
        for i in 0..16 {
            w[i] = be_u32(&padded, off + i * 4);
        }
        // Remaining 48 words: recurrence over positions 16..63
        // (TraversalEngine + Reduction-style mod-2^32 addition).
        for i in 16..64 {
            let s0 = small_sigma0(w[i - 15]);
            let s1 = small_sigma1(w[i - 2]);
            // Reduction over four terms under wrapping add (mod 2^32 is
            // associative-commutative; satisfies Reduction's invariant).
            w[i] = Reduction::reduce(vec![w[i - 16], s0, w[i - 7], s1], 0u32, |x, y| {
                x.wrapping_add(y)
            });
        }

        // Pull the 8 working variables out of the registry.
        let mut a = *state.lookup(&0).unwrap();
        let mut b_ = *state.lookup(&1).unwrap();
        let mut c = *state.lookup(&2).unwrap();
        let mut d = *state.lookup(&3).unwrap();
        let mut e = *state.lookup(&4).unwrap();
        let mut f = *state.lookup(&5).unwrap();
        let mut g = *state.lookup(&6).unwrap();
        let mut h = *state.lookup(&7).unwrap();

        // TraversalEngine over the 64 compression rounds. Each round is
        // an ActuationPass on the working state (combining the bitwise
        // mixing functions Ch/Maj/Σ0/Σ1 and Reduction over mod-2^32
        // sums).
        for i in 0..64 {
            let t1 = Reduction::reduce(
                vec![h, big_sigma1(e), ch(e, f, g), SHA256_K[i], w[i]],
                0u32,
                |x, y| x.wrapping_add(y),
            );
            let t2 = Reduction::reduce(vec![big_sigma0(a), maj(a, b_, c)], 0u32, |x, y| {
                x.wrapping_add(y)
            });
            h = g;
            g = f;
            f = e;
            e = d.wrapping_add(t1);
            d = c;
            c = b_;
            b_ = a;
            a = t1.wrapping_add(t2);
        }

        // Final state add: Reduction (mod-2^32) over the prior state
        // and the round output, written back to the registry.
        state.insert(0, state.lookup(&0).unwrap().wrapping_add(a));
        state.insert(1, state.lookup(&1).unwrap().wrapping_add(b_));
        state.insert(2, state.lookup(&2).unwrap().wrapping_add(c));
        state.insert(3, state.lookup(&3).unwrap().wrapping_add(d));
        state.insert(4, state.lookup(&4).unwrap().wrapping_add(e));
        state.insert(5, state.lookup(&5).unwrap().wrapping_add(f));
        state.insert(6, state.lookup(&6).unwrap().wrapping_add(g));
        state.insert(7, state.lookup(&7).unwrap().wrapping_add(h));
    });

    // Output: serialize state words 0..7 as big-endian into 32 bytes.
    let mut digest = [0u8; 32];
    for i in 0..8 {
        let w = *state.lookup(&i).unwrap();
        digest[i * 4..(i + 1) * 4].copy_from_slice(&be_u32_to_bytes(w));
    }
    digest
}

// =====================================================================
// SHA-3-256
// =====================================================================
//
// Absorb-then-squeeze sponge construction over the Keccak-f[1600]
// permutation. State = 1600 bits = 25 lanes of 64 bits;
// rate r = 1088 bits = 17 lanes; capacity c = 512 bits = 8 lanes.
// Padding: pad10*1 with SHA-3 domain separator (0x06 first padding byte,
// 0x80 final-block high bit; collapse to 0x86 when they coincide).
//
// Composition shape:
//   ResourceRegistry over the 25 state lanes.
//   TraversalEngine over input rate-blocks (absorb) and over the 24
//     permutation rounds.
//   ActuationPass per Keccak-f permutation step (a single call to
//     content::keccak::keccak_f1600 — the round is the unit of
//     ActuationPass at this level).
//   Reduction (XOR) for the absorb step's mix-into-rate.
//
// Structural ordering: Linear (sponge state is updated in order).
// Modality: Sequential within a hash invocation; Fork-join admissible
// across independent invocations.
//
// Endianness: little-endian (FIPS 202 §B.1) — distinct from SHA-256's
// big-endian convention.

const SHA3_256_RATE: usize = 1088 / 8; // 136 bytes (17 lanes × 8 bytes)
const SHA3_DOMAIN_SUFFIX: u8 = 0x06; // SHA-3 multi-rate suffix

/// SHA-3-256, built only from primitives + content.
pub fn sha3_256(msg: &[u8]) -> [u8; 32] {
    // ResourceRegistry: the 25 state lanes, indexed by position.
    // Held as a stack array for arithmetic speed; the registry
    // semantics are the same — one value per position.
    let mut state = [0u64; 25];

    // ---- Absorb full-rate blocks ----------------------------------
    // TraversalEngine over the input blocks (with bounded count =
    // floor(msg.len() / RATE)).
    let full_blocks = msg.len() / SHA3_256_RATE;
    TraversalEngine::iter_rounds(&mut state, full_blocks, |state, b| {
        let off = b * SHA3_256_RATE;
        // Reduction (XOR) of the block's 17 little-endian lanes into
        // the state's first 17 positions.
        for j in 0..SHA3_256_RATE / 8 {
            let lane = u64::from_le_bytes(msg[off + j * 8..off + j * 8 + 8].try_into().unwrap());
            state[j] ^= lane;
        }
        // ActuationPass: apply Keccak-f to the state. (The 24 internal
        // rounds are themselves a TraversalEngine + per-round
        // ActuationPass + Reduction — see content::keccak.)
        keccak_f1600(state);
    });

    // ---- Pad and absorb the final block ---------------------------
    let tail_start = full_blocks * SHA3_256_RATE;
    let tail_len = msg.len() - tail_start;
    let mut last = [0u8; SHA3_256_RATE];
    last[..tail_len].copy_from_slice(&msg[tail_start..]);
    // pad10*1 with domain separator (FIPS 202 §B.2). When tail_len ==
    // rate - 1 the suffix byte and the final 0x80 bit coincide and
    // collapse to 0x86 via the OR below.
    last[tail_len] = SHA3_DOMAIN_SUFFIX;
    last[SHA3_256_RATE - 1] |= 0x80;
    for j in 0..SHA3_256_RATE / 8 {
        let lane = u64::from_le_bytes(last[j * 8..j * 8 + 8].try_into().unwrap());
        state[j] ^= lane;
    }
    keccak_f1600(&mut state);

    // ---- Squeeze 32 bytes (single squeeze block; SHA-3-256 output
    //      fits in 4 lanes < rate). -----------------------------------
    let mut out = [0u8; 32];
    for j in 0..4 {
        out[j * 8..j * 8 + 8].copy_from_slice(&state[j].to_le_bytes());
    }
    out
}

// =====================================================================
// BLAKE3
// =====================================================================
//
// Tree-fold-of-chunks composition over the BLAKE3
// compression function (G function applied across 4 columns and 4
// diagonals in 7 rounds with inter-round message permutation).
//
// Composition shape:
//   ResourceRegistry over per-chunk states, chunk chaining values, and
//     per-tree-level intermediate chaining values.
//   TraversalEngine over chunks (parallelizable; Tree at the algorithm
//     level), blocks within each chunk (Linear within a chunk), and
//     the 7 rounds of each block compression.
//   ActuationPass per round (the G function, applied across columns
//     then diagonals).
//   Reduction (XOR) inside G and in the final output mixing.
//
// Structural ordering: Tree at the algorithm level (chunks combine up
// a binary tree); Linear within each chunk. Modality: Sequential as
// written; Fork-join admissible across the bottom-level chunks and
// within each tree level.
//
// Endianness: little-endian throughout.

const BLAKE3_CHUNK_SIZE: usize = 1024;
const BLAKE3_BLOCK_SIZE: usize = 64;

/// The BLAKE3 G function (BLAKE3 spec §2.1.2). Operates on four state
/// words `a`, `b`, `c`, `d` and consumes two message words `mx`, `my`.
/// Built from `Reduction` (`wrapping_add`) and bitwise XOR / rotate.
#[inline]
fn g(state: &mut [u32; 16], a: usize, b: usize, c: usize, d: usize, mx: u32, my: u32) {
    state[a] = state[a].wrapping_add(state[b]).wrapping_add(mx);
    state[d] = (state[d] ^ state[a]).rotate_right(16);
    state[c] = state[c].wrapping_add(state[d]);
    state[b] = (state[b] ^ state[c]).rotate_right(12);
    state[a] = state[a].wrapping_add(state[b]).wrapping_add(my);
    state[d] = (state[d] ^ state[a]).rotate_right(8);
    state[c] = state[c].wrapping_add(state[d]);
    state[b] = (state[b] ^ state[c]).rotate_right(7);
}

/// One round of BLAKE3 = 4 column G-calls + 4 diagonal G-calls.
/// (ActuationPass per call; total 8 G calls per round.)
fn blake3_round(state: &mut [u32; 16], m: &[u32; 16]) {
    // 4 columns
    g(state, 0, 4, 8, 12, m[0], m[1]);
    g(state, 1, 5, 9, 13, m[2], m[3]);
    g(state, 2, 6, 10, 14, m[4], m[5]);
    g(state, 3, 7, 11, 15, m[6], m[7]);
    // 4 diagonals
    g(state, 0, 5, 10, 15, m[8], m[9]);
    g(state, 1, 6, 11, 12, m[10], m[11]);
    g(state, 2, 7, 8, 13, m[12], m[13]);
    g(state, 3, 4, 9, 14, m[14], m[15]);
}

/// BLAKE3 message-schedule permutation σ (between rounds, except after
/// the final round).
fn blake3_permute(m: &mut [u32; 16]) {
    let mut out = [0u32; 16];
    for i in 0..16 {
        out[i] = m[BLAKE3_MSG_PERMUTATION[i]];
    }
    *m = out;
}

/// BLAKE3 compression function (BLAKE3 spec §2.1).
/// Returns the full 16-word output state; callers take either the
/// first 8 words (chaining-value path) or the full 16 (extended output).
fn compress(
    cv: &[u32; 8],
    block_words: &[u32; 16],
    counter: u64,
    block_len: u32,
    flags: u32,
) -> [u32; 16] {
    let mut state: [u32; 16] = [
        cv[0],
        cv[1],
        cv[2],
        cv[3],
        cv[4],
        cv[5],
        cv[6],
        cv[7],
        BLAKE3_IV[0],
        BLAKE3_IV[1],
        BLAKE3_IV[2],
        BLAKE3_IV[3],
        counter as u32,
        (counter >> 32) as u32,
        block_len,
        flags,
    ];
    let mut m = *block_words;

    // TraversalEngine over the 7 rounds. After each of the first 6
    // rounds, permute the message words; the 7th round does not permute.
    blake3_round(&mut state, &m);
    for _ in 0..6 {
        blake3_permute(&mut m);
        blake3_round(&mut state, &m);
    }

    // Final output mixing: state[0..8] ^= state[8..16] (Reduction-XOR);
    // state[8..16] ^= input CV (used by extended-output mode; harmless
    // for the 32-byte path which reads only state[0..8]).
    for i in 0..8 {
        state[i] ^= state[i + 8];
        state[i + 8] ^= cv[i];
    }
    state
}

/// Parse 64 bytes of a block into 16 little-endian u32 words.
fn block_bytes_to_words(block: &[u8; 64]) -> [u32; 16] {
    let mut words = [0u32; 16];
    for i in 0..16 {
        words[i] = u32::from_le_bytes(block[i * 4..i * 4 + 4].try_into().unwrap());
    }
    words
}

/// Process one chunk: chain up to 16 blocks under the BLAKE3 chunk
/// compression rules. The chunk counter is the chunk's index (0-based).
/// `is_root_chunk` adds the ROOT flag to the *last* block's compression
/// — used when the entire input fits in a single chunk.
fn process_chunk(input: &[u8], chunk_counter: u64, is_root_chunk: bool) -> [u32; 8] {
    debug_assert!(input.len() <= BLAKE3_CHUNK_SIZE);

    let mut cv = BLAKE3_IV;
    // Empty input still produces one compression (block_len = 0, both
    // CHUNK_START and CHUNK_END flags). Otherwise there's one block per
    // 64 bytes, rounded up for the partial last block.
    let block_count = if input.is_empty() {
        1
    } else {
        (input.len() + BLAKE3_BLOCK_SIZE - 1) / BLAKE3_BLOCK_SIZE
    };

    for block_idx in 0..block_count {
        let offset = block_idx * BLAKE3_BLOCK_SIZE;
        let block_end = (offset + BLAKE3_BLOCK_SIZE).min(input.len());
        let block_len = if input.is_empty() {
            0
        } else {
            block_end - offset
        };

        let mut block_bytes = [0u8; BLAKE3_BLOCK_SIZE];
        if !input.is_empty() {
            block_bytes[..block_len].copy_from_slice(&input[offset..block_end]);
        }
        let block_words = block_bytes_to_words(&block_bytes);

        let mut flags = 0u32;
        if block_idx == 0 {
            flags |= BLAKE3_FLAG_CHUNK_START;
        }
        if block_idx == block_count - 1 {
            flags |= BLAKE3_FLAG_CHUNK_END;
            if is_root_chunk {
                flags |= BLAKE3_FLAG_ROOT;
            }
        }

        let out = compress(&cv, &block_words, chunk_counter, block_len as u32, flags);
        // The chaining-value output for the next block is state[0..8].
        cv.copy_from_slice(&out[..8]);
    }

    cv
}

/// Combine two child CVs into a parent CV. `is_root` adds the ROOT flag
/// (used at the very top of the tree).
fn parent_cv(left: &[u32; 8], right: &[u32; 8], is_root: bool) -> [u32; 8] {
    // Block = left || right (16 u32 words / 64 bytes).
    let mut block = [0u32; 16];
    block[..8].copy_from_slice(left);
    block[8..].copy_from_slice(right);

    let mut flags = BLAKE3_FLAG_PARENT;
    if is_root {
        flags |= BLAKE3_FLAG_ROOT;
    }
    let out = compress(&BLAKE3_IV, &block, 0, BLAKE3_BLOCK_SIZE as u32, flags);

    let mut cv = [0u32; 8];
    cv.copy_from_slice(&out[..8]);
    cv
}

/// Recursive tree assembly. BLAKE3 splits a chunk list at the largest
/// power-of-two boundary strictly less than `len` (for non-power-of-two
/// lengths) or at `len/2` (for power-of-two lengths). Only the
/// outermost recursive call sets `is_root`.
fn tree_combine(cvs: &[[u32; 8]], is_root: bool) -> [u32; 8] {
    if cvs.len() == 1 {
        return cvs[0];
    }
    let n = cvs.len();
    let left_size = if n.is_power_of_two() {
        n / 2
    } else {
        n.next_power_of_two() >> 1
    };
    let (left_part, right_part) = cvs.split_at(left_size);
    let left = tree_combine(left_part, false);
    let right = tree_combine(right_part, false);
    parent_cv(&left, &right, is_root)
}

fn cv_to_bytes(cv: &[u32; 8]) -> [u8; 32] {
    let mut out = [0u8; 32];
    for i in 0..8 {
        out[i * 4..i * 4 + 4].copy_from_slice(&cv[i].to_le_bytes());
    }
    out
}

/// BLAKE3 (32-byte output), built only from primitives + content.
pub fn blake3_hash(input: &[u8]) -> [u8; 32] {
    let total_chunks = if input.is_empty() {
        1
    } else {
        (input.len() + BLAKE3_CHUNK_SIZE - 1) / BLAKE3_CHUNK_SIZE
    };

    if total_chunks == 1 {
        // Single-chunk fast path: the chunk IS the root.
        let cv = process_chunk(input, 0, true);
        return cv_to_bytes(&cv);
    }

    // Multi-chunk path: process each chunk as a non-root subtree, then
    // assemble the tree with the ROOT flag at the outermost parent.
    let mut chunk_cvs: Vec<[u32; 8]> = Vec::with_capacity(total_chunks);
    for chunk_idx in 0..total_chunks {
        let start = chunk_idx * BLAKE3_CHUNK_SIZE;
        let end = (start + BLAKE3_CHUNK_SIZE).min(input.len());
        let chunk_input = &input[start..end];
        chunk_cvs.push(process_chunk(chunk_input, chunk_idx as u64, false));
    }
    let root = tree_combine(&chunk_cvs, true);
    cv_to_bytes(&root)
}

// ---- Harness adapters --------------------------------------------------------

fn sha256_compose(input: Value) -> Value {
    let msg = input.as_bytes();
    Value::Bytes(sha256(&msg).to_vec())
}

fn sha3_256_compose(input: Value) -> Value {
    let msg = input.as_bytes();
    Value::Bytes(sha3_256(&msg).to_vec())
}

fn blake3_compose(input: Value) -> Value {
    let msg = input.as_bytes();
    Value::Bytes(blake3_hash(&msg).to_vec())
}

// ---- Registry ----------------------------------------------------------------

pub fn add(r: &mut Vec<CorpusEntry>) {
    entry(
        r,
        "sha256",
        "hash",
        1,
        "Linear",
        "ResourceRegistry + TraversalEngine + ActuationPass + Reduction (mod-2^32)",
        sha256_compose,
        "sha256",
        Equiv::Exact,
        gen::random_byte_messages,
    );
    entry(
        r,
        "sha3_256",
        "hash",
        1,
        "Linear",
        "ResourceRegistry (25 lanes) + TraversalEngine (rate blocks; 24 permutation rounds) + ActuationPass (Keccak-f) + Reduction (XOR absorb)",
        sha3_256_compose,
        "sha3_256",
        Equiv::Exact,
        gen::random_byte_messages,
    );
    entry(
        r,
        "blake3",
        "hash",
        1,
        "Tree (chunks), Linear (within chunk)",
        "ResourceRegistry (per-chunk CV + tree levels) + TraversalEngine (chunks, blocks, 7 rounds, tree levels) + ActuationPass (G-function) + Reduction (XOR/wrapping_add)",
        blake3_compose,
        "blake3",
        Equiv::Exact,
        gen::random_byte_messages,
    );
}

// ---- Unit tests against the canonical short test vectors -------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::hex_encode;

    /// Empty-string vector: NIST CAVP / FIPS 180-4.
    #[test]
    fn sha256_empty_string() {
        let got = sha256(b"");
        assert_eq!(
            hex_encode(&got),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
    }

    /// FIPS 180-4 Appendix B.1: "abc".
    #[test]
    fn sha256_abc() {
        let got = sha256(b"abc");
        assert_eq!(
            hex_encode(&got),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
    }

    /// FIPS 180-4 Appendix B.2: 448-bit message
    /// "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq".
    #[test]
    fn sha256_448_bit_message() {
        let msg = b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";
        let got = sha256(msg);
        assert_eq!(
            hex_encode(&got),
            "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
        );
    }

    // ---- SHA-3-256 KAT vectors ----

    /// FIPS 202 / NIST CAVP empty-string vector.
    #[test]
    fn sha3_256_empty_string() {
        let got = sha3_256(b"");
        assert_eq!(
            hex_encode(&got),
            "a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a"
        );
    }

    /// NIST CAVP "abc" vector for SHA-3-256.
    #[test]
    fn sha3_256_abc() {
        let got = sha3_256(b"abc");
        assert_eq!(
            hex_encode(&got),
            "3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe24511431532"
        );
    }

    /// NIST CAVP 448-bit vector (same message as the SHA-256 test).
    #[test]
    fn sha3_256_448_bit_message() {
        let msg = b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";
        let got = sha3_256(msg);
        assert_eq!(
            hex_encode(&got),
            "41c0dba2a9d6240849100376a8235e2c82e1b9998a999e21db32dd97496d3376"
        );
    }

    // ---- BLAKE3 KAT vectors ----

    /// BLAKE3 official test_vectors.json: input length 0.
    #[test]
    fn blake3_empty_string() {
        let got = blake3_hash(b"");
        assert_eq!(
            hex_encode(&got),
            "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"
        );
    }

    /// BLAKE3 over "abc".  Verified against the BLAKE3 reference
    /// (single-chunk, single-block path).
    #[test]
    fn blake3_abc() {
        let got = blake3_hash(b"abc");
        assert_eq!(
            hex_encode(&got),
            "6437b3ac38465133ffb63b75273a8db548c558465d79db03fd359c6cd5bd9d85"
        );
    }
}
