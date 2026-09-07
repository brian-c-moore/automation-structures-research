// TwoLayerWrap (HMAC).
//
// HMAC's two-layer wrap construction:
//   inner = H((K XOR ipad) || message)
//   outer = H((K XOR opad) || inner)
// The TLAPS proof at supplementary-research/studies/domain-corpora/cryptography/tla/compositions/TwoLayerWrap_Proof.tla
// closes 563 obligations using the chain pattern twice (once per phase).
//
// For Verus, two `iterate` calls suffice. The inner phase folds
// (K XOR ipad)-prefixed inputs; the outer phase folds
// (K XOR opad)-prefixed inner result.
//
// Verification boundary: written contracts plus named external-body assumptions.

use crate::compositions::iterated_transformation::{iterate, iterate_spec};
use vstd::prelude::*;

verus! {

pub const IPAD: u64 = 0x3636363636363636u64;
pub const OPAD: u64 = 0x5C5C5C5C5C5C5C5Cu64;

/// HMAC's mathematical specification: inner hash then outer hash with
/// the inner result as the single input to the outer fold. Both layers
/// reuse `iterate_spec` from `iterated_transformation`.
pub open spec fn hmac_spec(key: u64, message: Seq<u64>) -> u64 {
    let inner = iterate_spec(key ^ IPAD, message, message.len() as int);
    iterate_spec(key ^ OPAD, seq![inner], 1)
}

/// HMAC's two-layer hash: hash (K XOR ipad || msg), then hash
/// (K XOR opad || inner_result). The result is the MAC.
pub fn hmac(key: u64, message: &[u64]) -> (mac: u64)
    ensures mac == hmac_spec(key, message@),
{
    let inner_state = key ^ IPAD;
    let inner_result = iterate(inner_state, message);
    let outer_state = key ^ OPAD;
    let inner_vec: Vec<u64> = vec![inner_result];
    let result = iterate(outer_state, inner_vec.as_slice());
    proof {
        assert(inner_vec@ =~= seq![inner_result]);
    }
    result
}

}
