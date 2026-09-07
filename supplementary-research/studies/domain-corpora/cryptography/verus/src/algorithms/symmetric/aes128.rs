// AES-128 (FIPS 197).
//
// AES-128 instantiates iterated-transformation-over-chained-state.
// State = 16 bytes (4×4 byte matrix). The encryption pipeline:
//   K = (K_0, K_1, ..., K_10) — 11 round keys from FIPS 197 §5.2 key expansion
//   s_0 = AddRoundKey(plaintext, K_0)              // initial whitening
//   s_i = InnerRound(s_{i-1}, K_i)  for i = 1..9   // chain
//   ct  = FinalRound(s_9, K_10)                    // final (no MixColumns)
//   where InnerRound = SubBytes ∘ ShiftRows ∘ MixColumns ∘ AddRoundKey
//   and   FinalRound = SubBytes ∘ ShiftRows ∘ AddRoundKey.
//
// The chain shape is verified concretely: the 9-inner-round iteration is
// captured by recursive `aes_iter_inner_rounds_spec` and verified
// against the executable via loop invariant. Initial AddRoundKey,
// final round, and key expansion are uninterp + external_body; the
// FIPS 197 §5.1/§5.2 byte-level operations
// (SubBytes table lookup, ShiftRows permutation, MixColumns GF(2^8)
// multiplication, key schedule) are validated extrinsically via
// FIPS 197 Appendix C.1 KAT.
//
// Verification boundary: written contracts plus named external-body assumptions.

use vstd::prelude::*;

verus! {

pub const AES128_BLOCK_BYTES:    usize = 16;
pub const AES128_KEY_BYTES:      usize = 16;
pub const AES128_ROUND_KEYS:     usize = 11;
pub const AES128_EXPANDED_BYTES: usize = 176;
pub const AES128_NUM_ROUNDS:     usize = 10;
pub const AES128_NUM_INNER_ROUNDS: usize = 9;

/// AES S-box (FIPS 197 §5.1.1 Table 4).
pub const AES_SBOX: [u8; 256] = [
    0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
    0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
    0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
    0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,
    0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
    0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
    0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
    0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,
    0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
    0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
    0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
    0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
    0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
    0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,
    0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
    0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16,
];

/// AES Rcon (FIPS 197 §5.2 key expansion).
pub const AES_RCON: [u8; 11] = [
    0x00, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36,
];

// ── inner-round spec ───────────────────────────────────────────

/// inner_round_spec: SubBytes ∘ ShiftRows ∘ MixColumns ∘ AddRoundKey
/// (FIPS 197 §5.1.4). Uninterp; the concrete S-box +
/// ShiftRows + MixColumns + AddRoundKey is in external-body code.
pub uninterp spec fn inner_round_spec(state: Seq<u8>, round_key: Seq<u8>) -> Seq<u8>;

/// initial_add_round_key_spec: AddRoundKey(plaintext, K_0).
pub uninterp spec fn initial_add_round_key_spec(state: Seq<u8>, round_key: Seq<u8>) -> Seq<u8>;

/// final_round_spec: SubBytes ∘ ShiftRows ∘ AddRoundKey (FIPS 197
/// §5.1; final round omits MixColumns).
pub uninterp spec fn final_round_spec(state: Seq<u8>, round_key: Seq<u8>) -> Seq<u8>;

/// key_expand_spec: KeyExpansion (FIPS 197 §5.2).
pub uninterp spec fn key_expand_spec(key: Seq<u8>) -> Seq<u8>;

/// round_key_at_spec(expanded_keys, i): the 16-byte round key K_i
/// extracted from the 176-byte expanded-key schedule.
pub open spec fn round_key_at_spec(expanded: Seq<u8>, i: int) -> Seq<u8> {
    Seq::<u8>::new(16, |j: int| expanded[i * 16 + j])
}

// ── chain spec ─────────────────────────────────────────────────

/// aes_iter_inner_rounds_spec(state, expanded, n): the state after
/// `n` consecutive InnerRounds with keys K_1..K_n drawn from the
/// expanded key schedule. Recursive; mirrors iterate_spec.
pub open spec fn aes_iter_inner_rounds_spec(state: Seq<u8>, expanded: Seq<u8>, n: int) -> Seq<u8>
    decreases n,
{
    if n <= 0 {
        state
    } else {
        inner_round_spec(
            aes_iter_inner_rounds_spec(state, expanded, n - 1),
            round_key_at_spec(expanded, n),
        )
    }
}

/// aes128_encrypt_block_spec: full AES-128 encrypt (FIPS 197 §5.1).
pub open spec fn aes128_encrypt_block_spec(key: Seq<u8>, plaintext: Seq<u8>) -> Seq<u8> {
    let expanded = key_expand_spec(key);
    let s0 = initial_add_round_key_spec(plaintext, round_key_at_spec(expanded, 0));
    let s9 = aes_iter_inner_rounds_spec(s0, expanded, 9);
    final_round_spec(s9, round_key_at_spec(expanded, 10))
}

// ── External-body inner content ─────────────────────────────────────

#[verifier::external_body]
fn xtime(b: u8) -> u8 {
    if (b & 0x80) != 0 { (b << 1) ^ 0x1b } else { b << 1 }
}

#[verifier::external_body]
fn sub_word(w: u32) -> u32 {
    let b0 = AES_SBOX[((w >> 24) & 0xff) as usize] as u32;
    let b1 = AES_SBOX[((w >> 16) & 0xff) as usize] as u32;
    let b2 = AES_SBOX[((w >>  8) & 0xff) as usize] as u32;
    let b3 = AES_SBOX[( w        & 0xff) as usize] as u32;
    (b0 << 24) | (b1 << 16) | (b2 << 8) | b3
}

#[verifier::external_body]
fn rot_word(w: u32) -> u32 {
    (w << 8) | (w >> 24)
}

#[verifier::external_body]
pub fn aes128_key_expand(key: &[u8; 16]) -> (out: [u8; 176])
    ensures out@ == key_expand_spec(key@),
{
    let mut w: [u32; 44] = [0u32; 44];
    for i in 0..4 {
        w[i] = ((key[i * 4]     as u32) << 24)
             | ((key[i * 4 + 1] as u32) << 16)
             | ((key[i * 4 + 2] as u32) <<  8)
             | (key[i * 4 + 3] as u32);
    }
    for i in 4..44 {
        let mut t = w[i - 1];
        if i % 4 == 0 {
            t = sub_word(rot_word(t)) ^ ((AES_RCON[i / 4] as u32) << 24);
        }
        w[i] = w[i - 4] ^ t;
    }
    let mut out: [u8; 176] = [0u8; 176];
    for i in 0..44 {
        out[i * 4]     = (w[i] >> 24) as u8;
        out[i * 4 + 1] = (w[i] >> 16) as u8;
        out[i * 4 + 2] = (w[i] >>  8) as u8;
        out[i * 4 + 3] =  w[i]        as u8;
    }
    out
}

#[verifier::external_body]
fn add_round_key_inplace(state: &mut [u8; 16], rk: &[u8; 176], offset: usize) {
    for i in 0..16 {
        state[i] ^= rk[offset + i];
    }
}

#[verifier::external_body]
fn sub_bytes_inplace(state: &mut [u8; 16]) {
    for i in 0..16 {
        state[i] = AES_SBOX[state[i] as usize];
    }
}

#[verifier::external_body]
fn shift_rows_inplace(state: &mut [u8; 16]) {
    let t = state[1];
    state[1]  = state[5];  state[5]  = state[9];
    state[9]  = state[13]; state[13] = t;
    let t1 = state[2]; let t2 = state[6];
    state[2]  = state[10]; state[6]  = state[14];
    state[10] = t1;        state[14] = t2;
    let t = state[15];
    state[15] = state[11]; state[11] = state[7];
    state[7]  = state[3];  state[3]  = t;
}

#[verifier::external_body]
fn mix_columns_inplace(state: &mut [u8; 16]) {
    for c in 0..4 {
        let s0 = state[c * 4];
        let s1 = state[c * 4 + 1];
        let s2 = state[c * 4 + 2];
        let s3 = state[c * 4 + 3];
        let t = s0 ^ s1 ^ s2 ^ s3;
        let u = s0;
        state[c * 4]     ^= t ^ xtime(s0 ^ s1);
        state[c * 4 + 1] ^= t ^ xtime(s1 ^ s2);
        state[c * 4 + 2] ^= t ^ xtime(s2 ^ s3);
        state[c * 4 + 3] ^= t ^ xtime(s3 ^ u);
    }
}

// ── External-body per-round wrappers, ensures-linked to spec ────────

#[verifier::external_body]
pub fn aes_initial_round(state: &mut [u8; 16], expanded: &[u8; 176])
    ensures final(state)@ == initial_add_round_key_spec(
        old(state)@, round_key_at_spec(expanded@, 0)),
{
    add_round_key_inplace(state, expanded, 0);
}

#[verifier::external_body]
pub fn aes_inner_round(state: &mut [u8; 16], expanded: &[u8; 176], round: usize)
    requires 1 <= round <= 9,
    ensures final(state)@ == inner_round_spec(
        old(state)@, round_key_at_spec(expanded@, round as int)),
{
    sub_bytes_inplace(state);
    shift_rows_inplace(state);
    mix_columns_inplace(state);
    add_round_key_inplace(state, expanded, round * AES128_BLOCK_BYTES);
}

#[verifier::external_body]
pub fn aes_final_round(state: &mut [u8; 16], expanded: &[u8; 176])
    ensures final(state)@ == final_round_spec(
        old(state)@, round_key_at_spec(expanded@, 10)),
{
    sub_bytes_inplace(state);
    shift_rows_inplace(state);
    add_round_key_inplace(state, expanded, 10 * AES128_BLOCK_BYTES);
}

// ── Verified 9-inner-round iteration ──────────────────────────

/// aes_iterate_inner: 9 consecutive inner rounds, verified against
/// `aes_iter_inner_rounds_spec`.
pub fn aes_iterate_inner(state: &mut [u8; 16], expanded: &[u8; 176])
    ensures final(state)@ == aes_iter_inner_rounds_spec(old(state)@, expanded@, 9),
{
    let ghost initial = old(state)@;
    let mut r: usize = 1;
    while r <= 9
        invariant
            1 <= r <= 10,
            state@ == aes_iter_inner_rounds_spec(initial, expanded@, (r as int) - 1),
        decreases 10 - r,
    {
        aes_inner_round(state, expanded, r);
        r = r + 1;
    }
    proof {
        assert(state@ == aes_iter_inner_rounds_spec(initial, expanded@, 9));
    }
}

// ── Top-level AES-128 encrypt-block: verified composition ──────────

pub fn aes128_encrypt_block(key: &[u8; 16], plaintext: &[u8; 16]) -> (ct: [u8; 16])
    ensures ct@ == aes128_encrypt_block_spec(key@, plaintext@),
{
    let expanded = aes128_key_expand(key);
    let mut state: [u8; 16] = *plaintext;
    aes_initial_round(&mut state, &expanded);
    aes_iterate_inner(&mut state, &expanded);
    aes_final_round(&mut state, &expanded);
    state
}

}
