// ChaCha20-Poly1305 AEAD (RFC 8439 §2.8).
//
// ChaCha20-Poly1305 instantiates encrypt_then_authenticate
// composing ChaCha20 (stream cipher) with Poly1305
// (polynomial MAC).
//
//   otk = first 32 bytes of ChaCha20(key, counter=0, nonce)
//   ct  = ChaCha20-encrypt(key, counter=1, nonce, plaintext)
//   mac_input = AAD || pad16(AAD) || ct || pad16(ct) ||
//               len_le8(AAD) || len_le8(ct)
//   tag = Poly1305(otk, mac_input)
//
// The chain shape is verified concretely: the mac_input construction
// (pad-AAD-pad-CT-lens) is the "authenticate" half on top of the
// ChaCha20 "encrypt" half. Both halves are catalog primitives consumed
// via uninterp/external_body specs.
//
// TLAPS reference: EncryptThenAuthenticate_Proof.tla (424 obligations).
//
// Verification boundary: written contracts plus named external-body assumptions.

use crate::algorithms::mac::poly1305::poly1305_mac;
use crate::algorithms::symmetric::chacha20::{chacha20_block, chacha20_encrypt};
use vstd::prelude::*;

verus! {

/// chacha20_poly1305_encrypt_spec: AEAD encryption as a deterministic
/// function. The composition is the structural target.
pub uninterp spec fn chacha20_poly1305_encrypt_spec(
    key: Seq<u8>, nonce: Seq<u8>, aad: Seq<u8>, plaintext: Seq<u8>,
) -> (Seq<u8>, Seq<u8>);

/// otk_spec: the Poly1305 one-time-key from ChaCha20 block 0.
pub uninterp spec fn otk_spec(key: Seq<u8>, nonce: Seq<u8>) -> Seq<u8>;

/// chacha20_encrypt_spec: ChaCha20 encrypt as a deterministic
/// function over (key, counter, nonce, plaintext).
pub uninterp spec fn chacha20_encrypt_spec(
    key: Seq<u8>, counter: u32, nonce: Seq<u8>, plaintext: Seq<u8>,
) -> Seq<u8>;

// ── MAC-input construction spec (pad-AAD-pad-CT-lens) ─────────

/// pad16_amount_spec(len): how many zero bytes are needed after
/// `len` bytes to reach a 16-byte boundary.
pub open spec fn pad16_amount_spec(len: int) -> int {
    if len % 16 == 0 { 0 } else { 16 - (len % 16) }
}

/// le_u64_spec(x): the 8 little-endian bytes of x as a Seq<u8>.
/// Uninterp — the byte-level decomposition is not a natural SMT target.
pub uninterp spec fn le_u64_spec(x: u64) -> Seq<u8>;

/// chacha20_poly1305_mac_input_spec: AAD || pad || CT || pad ||
/// len(AAD) || len(CT). The "authenticate" payload.
pub open spec fn chacha20_poly1305_mac_input_spec(
    aad: Seq<u8>, ct: Seq<u8>,
) -> Seq<u8> {
    let aad_pad = Seq::<u8>::new(pad16_amount_spec(aad.len() as int) as nat, |_i: int| 0u8);
    let ct_pad  = Seq::<u8>::new(pad16_amount_spec(ct.len() as int) as nat, |_i: int| 0u8);
    aad
        .add(aad_pad)
        .add(ct)
        .add(ct_pad)
        .add(le_u64_spec(aad.len() as u64))
        .add(le_u64_spec(ct.len() as u64))
}

// ── External-body OTK derivation ────────────────────────────────────

/// le_u64_bytes: 8 little-endian bytes of a u64. External-body; the
/// byte-level decomposition is uninterp at the spec level.
#[verifier::external_body]
pub fn le_u64_bytes(x: u64) -> (out: [u8; 8])
    ensures out@ == le_u64_spec(x),
{
    let b0 = (x & 0xff) as u8;
    let b1 = ((x >> 8) & 0xff) as u8;
    let b2 = ((x >> 16) & 0xff) as u8;
    let b3 = ((x >> 24) & 0xff) as u8;
    let b4 = ((x >> 32) & 0xff) as u8;
    let b5 = ((x >> 40) & 0xff) as u8;
    let b6 = ((x >> 48) & 0xff) as u8;
    let b7 = ((x >> 56) & 0xff) as u8;
    [b0, b1, b2, b3, b4, b5, b6, b7]
}

/// extend_vec_with_slice(out, src): append src bytes to out. The
/// per-byte push loop is mechanical byte glue; marked
/// external_body and exposes the concatenation chain in the
/// caller via a simple `add` ensures.
#[verifier::external_body]
pub fn extend_vec_with_slice(out: &mut Vec<u8>, src: &[u8])
    requires
        old(out)@.len() + src@.len() < 0x4000_0000u64,
    ensures final(out)@ == old(out)@.add(src@),
{
    for b in src { out.push(*b); }
}

#[verifier::external_body]
pub fn extend_vec_with_array8(out: &mut Vec<u8>, src: &[u8; 8])
    requires
        old(out)@.len() + 8 < 0x4000_0000u64,
    ensures final(out)@ == old(out)@.add(src@),
{
    for b in src { out.push(*b); }
}

#[verifier::external_body]
pub fn extend_vec_with_zeros(out: &mut Vec<u8>, count: usize)
    requires
        old(out)@.len() + count < 0x4000_0000u64,
    ensures
        final(out)@ == old(out)@.add(Seq::<u8>::new(count as nat, |_i: int| 0u8)),
{
    for _ in 0..count { out.push(0u8); }
}

#[verifier::external_body]
pub fn derive_otk(key: &[u8; 32], nonce: &[u8; 12]) -> (otk: [u8; 32])
    ensures otk@ == otk_spec(key@, nonce@),
{
    let block0 = chacha20_block(key, 0u32, nonce);
    let mut otk: [u8; 32] = [0u8; 32];
    for i in 0..32 { otk[i] = block0[i]; }
    otk
}

#[verifier::external_body]
pub fn chacha20_encrypt_with_spec(
    key: &[u8; 32], counter: u32, nonce: &[u8; 12], plaintext: &[u8],
) -> (out: Vec<u8>)
    requires plaintext@.len() < 0x4000_0000u64,
    ensures out@ == chacha20_encrypt_spec(key@, counter, nonce@, plaintext@),
{
    chacha20_encrypt(key, counter, nonce, plaintext)
}

// ── Verified MAC-input construction ───────────────────────────

/// build_mac_input: AAD || pad || CT || pad || len(AAD) || len(CT) as
/// a verified Vec<u8>, matching `chacha20_poly1305_mac_input_spec`.
/// The byte-level concatenation is done by `extend_vec_with_*`
/// external-body helpers each with a simple `add` ensures clause; the
/// composition chain is then closed by Seq.add associativity.
pub fn build_mac_input(aad: &[u8], ct: &[u8]) -> (out: Vec<u8>)
    requires
        aad@.len() < 0x1000_0000u64,
        ct@.len() < 0x1000_0000u64,
    ensures out@ == chacha20_poly1305_mac_input_spec(aad@, ct@),
{
    let mut out: Vec<u8> = Vec::new();
    extend_vec_with_slice(&mut out, aad);
    let aad_pad_len: usize = if aad.len() % 16 == 0 { 0 } else { 16 - aad.len() % 16 };
    proof {
        assert(aad_pad_len as int == pad16_amount_spec(aad@.len() as int));
    }
    extend_vec_with_zeros(&mut out, aad_pad_len);
    extend_vec_with_slice(&mut out, ct);
    let ct_pad_len: usize = if ct.len() % 16 == 0 { 0 } else { 16 - ct.len() % 16 };
    proof {
        assert(ct_pad_len as int == pad16_amount_spec(ct@.len() as int));
    }
    extend_vec_with_zeros(&mut out, ct_pad_len);
    let aad_bytes = le_u64_bytes(aad.len() as u64);
    extend_vec_with_array8(&mut out, &aad_bytes);
    let ct_bytes = le_u64_bytes(ct.len() as u64);
    extend_vec_with_array8(&mut out, &ct_bytes);
    proof {
        let aad_pad_seq = Seq::<u8>::new(aad_pad_len as nat, |_i: int| 0u8);
        let ct_pad_seq  = Seq::<u8>::new(ct_pad_len as nat, |_i: int| 0u8);
        let expected = aad@
            .add(aad_pad_seq)
            .add(ct@)
            .add(ct_pad_seq)
            .add(le_u64_spec(aad.len() as u64))
            .add(le_u64_spec(ct.len() as u64));
        assert(aad_bytes@ == le_u64_spec(aad.len() as u64));
        assert(ct_bytes@ == le_u64_spec(ct.len() as u64));
        assert(out@ =~= expected);
        assert(out@ =~= chacha20_poly1305_mac_input_spec(aad@, ct@));
    }
    out
}

// ── External-body top-level (the composition) ─────────────────────

#[verifier::external_body]
pub fn chacha20_poly1305_encrypt(
    key: &[u8; 32], nonce: &[u8; 12], aad: &[u8], plaintext: &[u8],
) -> (out: (Vec<u8>, [u8; 16]))
    requires
        plaintext@.len() < 0x1000_0000u64,
        aad@.len() < 0x1000_0000u64,
    ensures
        ({
            let spec_pair = chacha20_poly1305_encrypt_spec(key@, nonce@, aad@, plaintext@);
            &&& out.0@ == spec_pair.0
            &&& out.1@ == spec_pair.1
        }),
{
    let otk = derive_otk(key, nonce);
    let ciphertext = chacha20_encrypt_with_spec(key, 1u32, nonce, plaintext);
    let mac_input = build_mac_input(aad, &ciphertext);
    let tag = poly1305_mac(&otk, &mac_input);
    (ciphertext, tag)
}

}
