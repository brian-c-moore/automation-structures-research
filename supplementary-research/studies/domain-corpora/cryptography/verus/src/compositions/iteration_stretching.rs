// IterationStretching (PBKDF2 inner loop).
//
// PBKDF2's per-block construction:
//   U_1 = HMAC(password, salt || block_idx)
//   U_j = HMAC(password, U_{j-1})  for j = 2..c
//   T   = U_1 XOR U_2 XOR ... XOR U_c
// where c is the iteration count. The TLAPS proof at
// supplementary-research/studies/domain-corpora/cryptography/tla/compositions/IterationStretching_Proof.tla closes
// 323 obligations capturing the chain-cannot-be-parallelized claim.
//
// For Verus, the per-block stretching is a fold over c iterations of
// HMAC, accumulating XOR. HMAC is modelled as the composition's
// `hmac_spec`; the structural correctness of PBKDF2 is the iterated
// composition.
//
// Verification boundary: written contracts plus named external-body assumptions.

use crate::compositions::two_layer_wrap::hmac_spec;
use vstd::prelude::*;

verus! {

/// One PBKDF2 block: c iterations of HMAC, with XOR accumulator.
///
/// Spec form: U_c is the c-th iterate of HMAC starting from
/// `salt || block_idx` (modeled here as the initial seed); the output
/// T is U_1 XOR U_2 XOR ... XOR U_c.
pub open spec fn pbkdf2_block_spec(password: u64, seed: u64, c: int) -> u64
    decreases c,
{
    if c <= 0 {
        0
    } else {
        // U_c: c iterations of HMAC starting from the seed.
        let u_c = pbkdf2_uvalue_spec(password, seed, c);
        u_c ^ pbkdf2_block_spec(password, seed, c - 1)
    }
}

pub open spec fn pbkdf2_uvalue_spec(password: u64, seed: u64, j: int) -> u64
    decreases j,
{
    if j <= 0 {
        seed
    } else if j == 1 {
        hmac_spec(password, seq![seed])
    } else {
        hmac_spec(password, seq![pbkdf2_uvalue_spec(password, seed, j - 1)])
    }
}

}
