// ExtractThenExpand (HKDF).
//
// HKDF's two-phase construction:
//   Extract:  PRK = HMAC(salt, IKM)
//   Expand:   T_0 = "" ; T_i = HMAC(PRK, T_{i-1} || info || i_byte)
//             OKM = T_1 || T_2 || ...
// The TLAPS proof at supplementary-research/studies/domain-corpora/cryptography/tla/compositions/
// ExtractThenExpand_Proof.tla closes 272 obligations.
//
// For Verus, both phases reuse `hmac_spec`. The extract phase
// is a single HMAC call; the expand phase is a fold of HMAC calls
// chained through the previous output.
//
// Verification boundary: written contracts plus named external-body assumptions.

use crate::compositions::two_layer_wrap::hmac_spec;
use vstd::prelude::*;

verus! {

/// HKDF Extract: PRK = HMAC(salt, IKM). One HMAC call.
pub open spec fn hkdf_extract_spec(salt: u64, ikm: u64) -> u64 {
    hmac_spec(salt, seq![ikm])
}

/// HKDF Expand: T_i = HMAC(PRK, T_{i-1} || info || i). Recursive on i.
/// The original HKDF chains T_{i-1}, info, and the counter byte into a
/// single HMAC input; the structural verification represents this as a
/// 2-element seq (the recursion captures the chain semantics).
pub open spec fn hkdf_expand_block_spec(prk: u64, info: u64, i: int) -> u64
    decreases i,
{
    if i <= 0 {
        0
    } else if i == 1 {
        hmac_spec(prk, seq![info, 1])
    } else {
        hmac_spec(prk, seq![hkdf_expand_block_spec(prk, info, i - 1), info, i as u64])
    }
}

/// Full HKDF: Extract then Expand. Returns the first output block T_1.
/// Longer outputs collect T_1, T_2, ..., T_k.
pub open spec fn hkdf_spec(salt: u64, ikm: u64, info: u64) -> u64 {
    let prk = hkdf_extract_spec(salt, ikm);
    hkdf_expand_block_spec(prk, info, 1)
}

}
