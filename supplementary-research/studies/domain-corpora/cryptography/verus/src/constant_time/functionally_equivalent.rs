// ConstantTimeFunctionallyEquivalent.
//
// Constant-time and variable-time Montgomery-ladder realizations
// produce identical (R0, R1) state at every bit index. The
// TLAPS proof at supplementary-research/studies/domain-corpora/cryptography/tla/constant_time/
// ConstantTimeFunctionallyEquivalent_Proof.tla closes 160 obligations
// via lockstep stepping; this Verus version mirrors that pattern.
//
// Modeling note. CT uses an IF-THEN-ELSE inside the assignment
// (modeling a branchless CSwap); VT uses an explicit if/else. Both
// produce the same output given the same input — the timing
// distinction is at the source-shape level, not at the
// functional-equivalence level (which Verus reasons about).

use vstd::prelude::*;

verus! {

pub const L: u64 = 4;
pub const SCALAR_BITS: usize = 4;
pub const G: u64 = 1;       // base point

/// Scalar bits, MSB-first, of 1011₂ = 11.
pub open spec fn scalar_bit(k: int) -> u64 {
    if k == 1 { 1 }
    else if k == 2 { 0 }
    else if k == 3 { 1 }
    else if k == 4 { 1 }
    else { 0 }
}

/// Lockstep refinement: at each bit, both ladders apply the same
/// per-step Montgomery-ladder transition (with bit-selection by
/// IF-THEN-ELSE in CT, explicit branch in VT). The two pre-states
/// are equal; the per-step transition is deterministic on its
/// inputs; therefore the two post-states are equal.
pub fn ladder_equivalent() -> (out: ((u64, u64), (u64, u64)))
    ensures
        out.0.0 == out.1.0,   // ct_R0 == vt_R0
        out.0.1 == out.1.1,   // ct_R1 == vt_R1
{
    let mut ct_r0: u64 = 0;
    let mut ct_r1: u64 = G;
    let mut vt_r0: u64 = 0;
    let mut vt_r1: u64 = G;
    let mut i: usize = 0;
    while i < SCALAR_BITS
        invariant
            i <= SCALAR_BITS,
            ct_r0 < L,
            ct_r1 < L,
            vt_r0 < L,
            vt_r1 < L,
            ct_r0 == vt_r0,
            ct_r1 == vt_r1,
        decreases SCALAR_BITS - i,
    {
        // Compute the bit explicitly (concrete model values).
        let bit: u64 = if i == 0 { 1 }
                       else if i == 1 { 0 }
                       else if i == 2 { 1 }
                       else { 1 };

        // CT: IF-THEN-ELSE inside the assignment (models branchless
        // CSwap-then-step).
        let ct_r0_new: u64 = if bit == 1 {
            (ct_r0 + ct_r1) % L
        } else {
            (ct_r0 + ct_r0) % L
        };
        let ct_r1_new: u64 = if bit == 1 {
            (ct_r1 + ct_r1) % L
        } else {
            (ct_r0 + ct_r1) % L
        };

        // VT: explicit branch.
        let vt_r0_new: u64;
        let vt_r1_new: u64;
        if bit == 1 {
            vt_r0_new = (vt_r0 + vt_r1) % L;
            vt_r1_new = (vt_r1 + vt_r1) % L;
        } else {
            vt_r0_new = (vt_r0 + vt_r0) % L;
            vt_r1_new = (vt_r0 + vt_r1) % L;
        }

        ct_r0 = ct_r0_new;
        ct_r1 = ct_r1_new;
        vt_r0 = vt_r0_new;
        vt_r1 = vt_r1_new;
        i = i + 1;
    }
    ((ct_r0, ct_r1), (vt_r0, vt_r1))
}

}
