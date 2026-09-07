// SHA-256.
//
// SHA-256 is the canonical instantiation of iterated-transformation
// over chained state. State = eight 32-bit words;
// inputs = 64-byte message blocks (16 big-endian words each); round
// function = the FIPS 180-4 §6.2 compression with the message-schedule
// expansion to 64 words and 64 SHA-256 rounds per block.
//
// Under the hybrid composition heuristic this module is self-contained:
// SHA-256's state shape (8 x u32) and round function differ from the
// base composition's u64 state and additive round, so `iterate_spec` is
// the structural model (a recursive spec function for the chain), not a
// directly imported implementation. The chain pattern is reproduced
// inline.
//
// TLAPS reference: supplementary-research/studies/domain-corpora/cryptography/tla/compositions/
// IteratedTransformationOverChainedState_Proof.tla (156 obligations,
// cold-deterministic). The Verus translation collapses the TLAPS four-
// invariant conjunction to a single ensures clause: recursive specs
// replace sequence-history.
//
// Content sourced from FIPS 180-4 §4.2.2 (K constants) and §5.3.3 (H0
// initial state). The corresponding executable Rust at
// cryptography/rust/src/compositions/hashes.rs::sha256 has FIPS 180-4
// Appendix B test vectors; this module's tests/ cross-check exercises
// the same vectors against the Verus build of sha256().
//
// Verification boundary: written contracts plus named external-body assumptions.

use vstd::prelude::*;

verus! {

// ── FIPS 180-4 constants ─────────────────────────────────────────────

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
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

// ── Bitwise mixing functions (FIPS 180-4 §4.1.2) ─────────────────────

pub open spec fn ch_spec(x: u32, y: u32, z: u32) -> u32 {
    (x & y) ^ ((!x) & z)
}

pub fn ch(x: u32, y: u32, z: u32) -> (r: u32)
    ensures r == ch_spec(x, y, z),
{
    (x & y) ^ ((!x) & z)
}

pub open spec fn maj_spec(x: u32, y: u32, z: u32) -> u32 {
    (x & y) ^ (x & z) ^ (y & z)
}

pub fn maj(x: u32, y: u32, z: u32) -> (r: u32)
    ensures r == maj_spec(x, y, z),
{
    (x & y) ^ (x & z) ^ (y & z)
}

/// ROTR(x, n) = (x >> n) | (x << (32 - n)) for u32; the FIPS 180-4
/// rotate-right operator. wrapping_shr/shl keep the spec and exec
/// syntactically identical (vstd::wrapping defines both).
pub open spec fn rotr32_spec(x: u32, n: u32) -> u32 {
    x.wrapping_shr(n) | x.wrapping_shl(32u32.wrapping_sub(n))
}

pub fn rotr32(x: u32, n: u32) -> (r: u32)
    requires 0 < n < 32,
    ensures r == rotr32_spec(x, n),
{
    x.wrapping_shr(n) | x.wrapping_shl(32u32.wrapping_sub(n))
}

pub open spec fn big_sigma0_spec(x: u32) -> u32 {
    rotr32_spec(x, 2) ^ rotr32_spec(x, 13) ^ rotr32_spec(x, 22)
}

pub fn big_sigma0(x: u32) -> (r: u32)
    ensures r == big_sigma0_spec(x),
{
    rotr32(x, 2) ^ rotr32(x, 13) ^ rotr32(x, 22)
}

pub open spec fn big_sigma1_spec(x: u32) -> u32 {
    rotr32_spec(x, 6) ^ rotr32_spec(x, 11) ^ rotr32_spec(x, 25)
}

pub fn big_sigma1(x: u32) -> (r: u32)
    ensures r == big_sigma1_spec(x),
{
    rotr32(x, 6) ^ rotr32(x, 11) ^ rotr32(x, 25)
}

pub open spec fn small_sigma0_spec(x: u32) -> u32 {
    rotr32_spec(x, 7) ^ rotr32_spec(x, 18) ^ x.wrapping_shr(3)
}

pub fn small_sigma0(x: u32) -> (r: u32)
    ensures r == small_sigma0_spec(x),
{
    rotr32(x, 7) ^ rotr32(x, 18) ^ x.wrapping_shr(3)
}

pub open spec fn small_sigma1_spec(x: u32) -> u32 {
    rotr32_spec(x, 17) ^ rotr32_spec(x, 19) ^ x.wrapping_shr(10)
}

pub fn small_sigma1(x: u32) -> (r: u32)
    ensures r == small_sigma1_spec(x),
{
    rotr32(x, 17) ^ rotr32(x, 19) ^ x.wrapping_shr(10)
}

// ── State and round function ─────────────────────────────────────────

/// SHA-256 working state: the eight registers (a, b, c, d, e, f, g, h).
pub type SState = (u32, u32, u32, u32, u32, u32, u32, u32);

/// One SHA-256 compression round (FIPS 180-4 §6.2.2 step 3). Takes the
/// state (a, b, c, d, e, f, g, h), the round constant K[i] and the
/// schedule word W[i]; returns the rotated/updated state.
pub open spec fn round_spec(s: SState, k: u32, w: u32) -> SState {
    let t1 = s.7.wrapping_add(big_sigma1_spec(s.4))
        .wrapping_add(ch_spec(s.4, s.5, s.6))
        .wrapping_add(k)
        .wrapping_add(w);
    let t2 = big_sigma0_spec(s.0).wrapping_add(maj_spec(s.0, s.1, s.2));
    (
        t1.wrapping_add(t2),       // new a
        s.0,                       // new b
        s.1,                       // new c
        s.2,                       // new d
        s.3.wrapping_add(t1),      // new e
        s.4,                       // new f
        s.5,                       // new g
        s.6,                       // new h
    )
}

pub fn round_step(a: u32, b: u32, c: u32, d: u32,
                  e: u32, f: u32, g: u32, h: u32,
                  k: u32, w: u32) -> (out: SState)
    ensures out == round_spec((a, b, c, d, e, f, g, h), k, w),
{
    let t1 = h.wrapping_add(big_sigma1(e))
        .wrapping_add(ch(e, f, g))
        .wrapping_add(k)
        .wrapping_add(w);
    let t2 = big_sigma0(a).wrapping_add(maj(a, b, c));
    (
        t1.wrapping_add(t2),
        a,
        b,
        c,
        d.wrapping_add(t1),
        e,
        f,
        g,
    )
}

// ── Iterated rounds spec (the chain pattern) ────────────────────

/// rounds_spec(s, k_seq, w_seq, n): the SHA-256 working state after
/// applying `n` consecutive rounds, starting from `s`, with K[i] = k_seq[i]
/// and W[i] = w_seq[i]. Recursive over `n`; mirrors the base
/// composition's `iterate_spec`.
pub open spec fn rounds_spec(s: SState, k_seq: Seq<u32>, w_seq: Seq<u32>, n: int) -> SState
    decreases n,
{
    if n <= 0 {
        s
    } else if n > k_seq.len() as int || n > w_seq.len() as int {
        s
    } else {
        let prev = rounds_spec(s, k_seq, w_seq, n - 1);
        round_spec(prev, k_seq[n - 1], w_seq[n - 1])
    }
}

// ── Message schedule W[0..64] spec ───────────────────────────────────

/// w_at_spec(block, i): the SHA-256 message-schedule word W[i] for the
/// given 16-word block. W[0..16] = block[0..16]; W[i] for 16..64 is the
/// recurrence W[i] = sigma1(W[i-2]) + W[i-7] + sigma0(W[i-15]) + W[i-16].
pub open spec fn w_at_spec(block: Seq<u32>, i: int) -> u32
    decreases i,
{
    if i < 0 {
        0
    } else if i < 16 {
        block[i]
    } else if i >= 64 {
        0
    } else {
        small_sigma1_spec(w_at_spec(block, i - 2))
            .wrapping_add(w_at_spec(block, i - 7))
            .wrapping_add(small_sigma0_spec(w_at_spec(block, i - 15)))
            .wrapping_add(w_at_spec(block, i - 16))
    }
}

/// Executable schedule construction: builds W[0..64] from a 16-word
/// block using two loops (load + recurrence).
pub fn build_schedule(block: &[u32; 16]) -> (w: [u32; 64])
    ensures
        forall|i: int| 0 <= i < 64 ==> w@[i] == w_at_spec(block@, i),
{
    let mut w: [u32; 64] = [0u32; 64];
    let mut i: usize = 0;
    while i < 16
        invariant
            i <= 16,
            w@.len() == 64,
            block@.len() == 16,
            forall|j: int| 0 <= j < i as int ==> w@[j] == w_at_spec(block@, j),
        decreases 16 - i,
    {
        w[i] = block[i];
        proof {
            assert(w@[i as int] == block@[i as int]);
            assert(w@[i as int] == w_at_spec(block@, i as int));
        }
        i = i + 1;
    }
    while i < 64
        invariant
            16 <= i <= 64,
            w@.len() == 64,
            block@.len() == 16,
            forall|j: int| 0 <= j < i as int ==> w@[j] == w_at_spec(block@, j),
        decreases 64 - i,
    {
        let s0 = small_sigma0(w[i - 15]);
        let s1 = small_sigma1(w[i - 2]);
        let val = s1.wrapping_add(w[i - 7]).wrapping_add(s0).wrapping_add(w[i - 16]);
        proof {
            assert(w@[i as int - 2] == w_at_spec(block@, i as int - 2));
            assert(w@[i as int - 7] == w_at_spec(block@, i as int - 7));
            assert(w@[i as int - 15] == w_at_spec(block@, i as int - 15));
            assert(w@[i as int - 16] == w_at_spec(block@, i as int - 16));
            assert(val == w_at_spec(block@, i as int));
        }
        w[i] = val;
        i = i + 1;
    }
    w
}

// ── Block compression (64 rounds + final state-add) ──────────────────

/// compress_one_block(state, block): apply 64 SHA-256 rounds to the
/// schedule expanded from `block`, then add the resulting working state
/// back to the input `state` per-element (FIPS 180-4 §6.2.2 step 4).
pub fn compress_one_block(state: &[u32; 8], block: &[u32; 16]) -> (out: [u32; 8])
    ensures
        out@.len() == 8,
        ({
            let w = Seq::<u32>::new(64, |j: int| w_at_spec(block@, j));
            let initial: SState = (state@[0], state@[1], state@[2], state@[3],
                                   state@[4], state@[5], state@[6], state@[7]);
            let after = rounds_spec(initial, SHA256_K@, w, 64);
            &&& out@[0] == state@[0].wrapping_add(after.0)
            &&& out@[1] == state@[1].wrapping_add(after.1)
            &&& out@[2] == state@[2].wrapping_add(after.2)
            &&& out@[3] == state@[3].wrapping_add(after.3)
            &&& out@[4] == state@[4].wrapping_add(after.4)
            &&& out@[5] == state@[5].wrapping_add(after.5)
            &&& out@[6] == state@[6].wrapping_add(after.6)
            &&& out@[7] == state@[7].wrapping_add(after.7)
        }),
{
    let w_arr = build_schedule(block);
    let w_seq: Ghost<Seq<u32>> = Ghost(Seq::<u32>::new(64, |j: int| w_at_spec(block@, j)));
    proof {
        assert(w_arr@ =~= w_seq@);
    }

    let initial: Ghost<SState> = Ghost((state@[0], state@[1], state@[2], state@[3],
                                       state@[4], state@[5], state@[6], state@[7]));

    let mut a: u32 = state[0];
    let mut b: u32 = state[1];
    let mut c: u32 = state[2];
    let mut d: u32 = state[3];
    let mut e: u32 = state[4];
    let mut f: u32 = state[5];
    let mut g: u32 = state[6];
    let mut h: u32 = state[7];

    let mut i: usize = 0;
    while i < 64
        invariant
            i <= 64,
            w_arr@.len() == 64,
            SHA256_K@.len() == 64,
            initial@ == (state@[0], state@[1], state@[2], state@[3],
                         state@[4], state@[5], state@[6], state@[7]),
            forall|j: int| 0 <= j < 64 ==> w_arr@[j] == w_at_spec(block@, j),
            (a, b, c, d, e, f, g, h) == rounds_spec(initial@, SHA256_K@, w_arr@, i as int),
        decreases 64 - i,
    {
        let (na, nb, nc, nd, ne, nf, ng, nh) =
            round_step(a, b, c, d, e, f, g, h, SHA256_K[i], w_arr[i]);
        a = na; b = nb; c = nc; d = nd;
        e = ne; f = nf; g = ng; h = nh;
        i = i + 1;
    }

    let out: [u32; 8] = [
        state[0].wrapping_add(a),
        state[1].wrapping_add(b),
        state[2].wrapping_add(c),
        state[3].wrapping_add(d),
        state[4].wrapping_add(e),
        state[5].wrapping_add(f),
        state[6].wrapping_add(g),
        state[7].wrapping_add(h),
    ];
    proof {
        assert(w_arr@ =~= w_seq@);
    }
    out
}

// ── Full SHA-256: padding + iterate compress + serialize ─────────────

/// Big-endian load of a u32 from a 4-byte slice.
#[verifier::external_body]
fn be_u32(bytes: &[u8], offset: usize) -> (r: u32)
    requires
        offset + 4 <= bytes@.len(),
{
    u32::from_be_bytes([
        bytes[offset],
        bytes[offset + 1],
        bytes[offset + 2],
        bytes[offset + 3],
    ])
}

/// Big-endian store of a u32 into a 4-byte buffer.
#[verifier::external_body]
fn be_u32_to_bytes(w: u32) -> (out: [u8; 4]) {
    w.to_be_bytes()
}

/// Merkle-Damgaard padding (FIPS 180-4 §5.1.1): append 0x80, then zero
/// bytes, then the 64-bit big-endian length-in-bits so the total length
/// is a multiple of 64 bytes (512 bits).
#[verifier::external_body]
fn pad_md(msg: &[u8]) -> (padded: Vec<u8>)
    requires
        msg@.len() < 0x2000_0000_0000_0000u64,
    ensures
        padded@.len() % 64 == 0,
        padded@.len() >= 64,
{
    let bit_len: u64 = (msg.len() as u64).wrapping_mul(8);
    let mut padded: Vec<u8> = Vec::with_capacity(msg.len() + 72);
    padded.extend_from_slice(msg);
    padded.push(0x80u8);
    while padded.len() % 64 != 56 {
        padded.push(0u8);
    }
    padded.extend_from_slice(&bit_len.to_be_bytes());
    padded
}

/// sha256_spec: the SHA-256 hash function as a deterministic mapping
/// over message bytes. Used by downstream modules (HMAC, HKDF, PBKDF2)
/// to reason about sha256() as a primitive in their chain shapes.
pub uninterp spec fn sha256_spec(message: Seq<u8>) -> Seq<u8>;

/// Full SHA-256: pad, iterate the block compression, serialize the
/// final state as 32 big-endian bytes. The structural correctness of
/// the compression is verified above; the padding and serialization
/// are mechanical and validated extrinsically by FIPS 180-4 test
/// vectors (see `tests/sha256_kat.rs`).
#[verifier::external_body]
pub fn sha256(msg: &[u8]) -> (digest: [u8; 32])
    requires
        msg@.len() < 0x2000_0000_0000_0000u64,
    ensures digest@ == sha256_spec(msg@),
{
    let padded = pad_md(msg);
    let mut state: [u32; 8] = SHA256_H0;
    let blocks = padded.len() / 64;
    let mut b: usize = 0;
    while b < blocks {
        let off = b * 64;
        let mut block: [u32; 16] = [0u32; 16];
        for j in 0..16 {
            block[j] = be_u32(padded.as_slice(), off + j * 4);
        }
        state = compress_one_block(&state, &block);
        b = b + 1;
    }
    let mut digest: [u8; 32] = [0u8; 32];
    for k in 0..8 {
        let bytes = be_u32_to_bytes(state[k]);
        digest[k * 4] = bytes[0];
        digest[k * 4 + 1] = bytes[1];
        digest[k * 4 + 2] = bytes[2];
        digest[k * 4 + 3] = bytes[3];
    }
    digest
}

}
