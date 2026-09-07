// CommitChallengeResponse (Ed25519, Schnorr).
//
// Three-phase signature flow with Fiat-Shamir challenge:
//   commit:    R = scalar_mult(r_nonce, G)
//   challenge: c = Hash(R, A, M)
//   response:  s = r_nonce + c * a_secret  (mod L)
// Verification: s * G == R + c * A.
//
// The TLAPS proof is decomposed into three modules (flow,
// distributivity, verification-equation bridge), closing
// 263 + 45 + 35 = 343 obligations. The algebraic-identity module uses
// integer Z/L arithmetic.
//
// For Verus, the integer-Z/L approach is replicated. The verification
// equation is a single concrete equality in the bounded model:
// s * G == R + c * A reduces to 1 == (3 + 2) mod 4 == 1 for r_nonce=3,
// a_secret=2, c_scalar=1 — the same arithmetic instance the TLAPS
// proof closes.
//
// This module consumes `scalar_multiplication`'s group operators: the
// Z/L = Z/4Z arithmetic, group_op, and the scalar-mult specifier are
// imported rather than re-defined here. Direct reuse is possible
// because that module's L and group_op are byte-identical with what is
// needed here.
//
// Verification boundary: written contracts plus named external-body assumptions.

use crate::compositions::scalar_multiplication::{group_op, L};
use vstd::prelude::*;

verus! {

/// Scalar-ring multiplication on Z/L. (Distinct from
/// `scalar_multiplication`'s scalar_mult, which is k*P group-element
/// multiplication; this is a*b on the scalar ring.) Local to this
/// module since `scalar_multiplication` does not expose it.
pub open spec fn scalar_mul_z4(a: u64, b: u64) -> u64 {
    ((a * b) % (L as int)) as u64
}

/// ScalarMult on Z/4Z: k * P = (k * P) mod L. Same as `group_op` when
/// one operand is "the scalar" and the other is
/// "the group element", under the Z/L cyclic-group representation.
pub open spec fn scalar_mult_z4(k: u64, p: u64) -> u64 {
    scalar_mul_z4(k, p)
}

/// Signature parameters (concrete model values, mirror of the TLAPS
/// CommitChallengeResponse modules).
pub const G: u64 = 1;        // base point
pub const A: u64 = 2;        // public key (= a_secret * G = 2 * 1 = 2)
pub const A_SECRET: u64 = 2; // private key scalar
pub const R_NONCE: u64 = 3;  // signature nonce
pub const C_SCALAR: u64 = 1; // challenge scalar (Hash output in the model)

/// Derived signature values (from the deterministic flow):
///   R_point  = scalar_mult(r_nonce, G)    = 3 * 1 mod 4 = 3
///   s_scalar = (r_nonce + c * a_secret)   = (3 + 1*2) mod 4 = 1
pub open spec fn r_point_spec() -> u64 {
    scalar_mult_z4(R_NONCE, G)
}

pub open spec fn s_scalar_spec() -> u64 {
    ((R_NONCE + scalar_mul_z4(C_SCALAR, A_SECRET)) % (L as int)) as u64
}

/// Verification equation: s * G == R + c * A. Both sides evaluate to 1.
pub fn verify_signature() -> (b: bool)
    ensures b == true,
{
    let r_point: u64 = (R_NONCE * G) % L;          // = 3
    let s_scalar: u64 = (R_NONCE + (C_SCALAR * A_SECRET) % L) % L; // = 1
    let lhs: u64 = (s_scalar * G) % L;             // = 1
    let rhs: u64 = (r_point + (C_SCALAR * A) % L) % L; // = (3 + 2) % 4 = 1
    lhs == rhs
}

}
