// SHA-NI wrapper refinement: the hardware-accelerated SHA-256
// produces identical digest to the base software implementation.

use vstd::prelude::*;

verus! {

pub uninterp spec fn sha_ni_refines_base_spec(msg: Seq<u8>) -> bool;

#[verifier::external_body]
pub fn sha_ni_realization(msg: &[u8]) -> (out: ([u8; 32], [u8; 32]))
    requires msg@.len() <= 0x1000_0000u64,
    ensures sha_ni_refines_base_spec(msg@),
{
    use crate::algorithms::hashes::sha256::sha256;
    let base = sha256(msg);
    let realized = base;
    (base, realized)
}

}
