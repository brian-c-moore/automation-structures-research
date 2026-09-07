// Constant-time discipline at the implementation layer.
//
// Mirror of supplementary-research/studies/domain-corpora/cryptography/tla/constant_time/ConstantTimeFunctionallyEquivalent_Proof.tla
// (160 obligations cold-deterministic). Both ladders compute the same
// per-step Montgomery-ladder transition; the CT version uses
// IF-THEN-ELSE inside the assignment (modeling a branchless CSwap)
// while the VT version uses an explicit branch. Lockstep stepping
// over a shared bit index makes the refinement invariant
// (`ct_R0 == vt_R0 /\ ct_R1 == vt_R1`) unconditional and inductive.
//
// With lockstep stepping for refinement specs, this module verifies
// the functional-equivalence claim; the
// constant-time *timing* property is structural in the source — the
// CT branch always evaluates both alternatives and selects via
// IF-THEN-ELSE — and is verified at the source-shape level rather
// than via Verus's dataflow.

pub mod functionally_equivalent;
pub mod bitsliced_aes_ct;
pub mod ct_select;
pub mod sig_equality;
pub mod x25519_ladder;
