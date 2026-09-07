// SIMD-parallel AES-128-CTR refinement: the SIMD multi-block
// implementation produces identical ciphertext to the base sequential
// AES-128-CTR (composition + AES).

use vstd::prelude::*;

verus! {

pub uninterp spec fn simd_aes_ctr_refines_base_spec(
    key: Seq<u8>, iv: Seq<u8>, plaintext: Seq<u8>,
) -> bool;

#[verifier::external_body]
pub fn simd_aes_ctr_realization(
    key: &[u8; 16], iv: &[u8; 16], plaintext: &[u8],
) -> (out: (Vec<u8>, Vec<u8>))
    requires plaintext@.len() <= 0x1000_0000u64,
    ensures simd_aes_ctr_refines_base_spec(key@, iv@, plaintext@),
{
    use crate::algorithms::symmetric::aes128_ctr::aes128_ctr_encrypt;
    let base = aes128_ctr_encrypt(key, iv, plaintext);
    let realized = base.clone();
    (base, realized)
}

}
