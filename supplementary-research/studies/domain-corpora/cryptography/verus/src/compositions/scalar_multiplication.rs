// ScalarMultiplicationOverGroup (RSA, Ed25519, X25519).
//
// Bit-by-bit double-and-add (or square-and-multiply for multiplicative
// groups). The TLAPS proof at supplementary-research/studies/domain-corpora/cryptography/tla/compositions/
// ScalarMultiplicationOverGroup_Proof.tla closes 161 obligations using
// the sequence-history chain pattern with a chained helper-lemma
// shape (GroupOpType -> RoundFnType).
//
// For Verus, the integer-arithmetic representation
// (GroupElement = 0..(L-1), GroupOp(a, b) = (a + b) % L) makes
// the algebraic identities tractable; the bijection with the model-
// value representation (ScalarMultiplicationOverGroup's g0..g3) preserves
// Z/L's structure.
//
// Verification boundary: written contracts plus named external-body assumptions.

use vstd::prelude::*;

verus! {

/// Group order L (cyclic group Z/L). Concrete bound for the model.
pub const L: u64 = 4;

pub open spec fn in_group(x: u64) -> bool {
    x < L
}

pub open spec fn group_op(a: u64, b: u64) -> u64 {
    ((a + b) % (L as int)) as u64
}

/// Scalar multiplication via double-and-add: at bit `i`, double the
/// accumulator and conditionally add the base point.
pub open spec fn scalar_mult_spec(scalar: Seq<u64>, base: u64, n: int) -> u64
    decreases n,
{
    if n <= 0 {
        0
    } else if n > scalar.len() as int {
        0
    } else {
        let acc_prev = scalar_mult_spec(scalar, base, n - 1);
        let doubled = group_op(acc_prev, acc_prev);
        if scalar[n - 1] == 1 {
            group_op(doubled, base)
        } else {
            doubled
        }
    }
}

/// Executable scalar multiplication. Bit-iteration with explicit
/// double-and-add. The loop invariant captures the chain-correctness
/// claim (acc = scalar_mult_spec at iteration i).
pub fn scalar_mult(scalar: &[u64], base: u64) -> (acc: u64)
    requires
        base < L,
        forall|i: int| 0 <= i < scalar@.len() ==> scalar@[i] <= 1,
    ensures acc == scalar_mult_spec(scalar@, base, scalar@.len() as int),
{
    let n: usize = scalar.len();
    let mut acc: u64 = 0;
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == scalar@.len(),
            base < L,
            acc < L,
            forall|j: int| 0 <= j < scalar@.len() ==> scalar@[j] <= 1,
            acc == scalar_mult_spec(scalar@, base, i as int),
        decreases n - i,
    {
        // Double.
        assert(acc + acc <= 6) by (nonlinear_arith)
            requires acc < L, L == 4;
        let doubled = (acc + acc) % L;
        // Conditional add.
        let bit = scalar[i];
        let new_acc = if bit == 1 {
            (doubled + base) % L
        } else {
            doubled
        };
        acc = new_acc;
        i = i + 1;
    }
    acc
}

}
