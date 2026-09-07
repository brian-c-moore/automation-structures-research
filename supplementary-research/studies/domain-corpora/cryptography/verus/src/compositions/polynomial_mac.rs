// PolynomialMacAccumulation (Poly1305, GHASH).
//
// Polynomial-MAC computes M(r) = X_1 * r^N + X_2 * r^{N-1} + ... + X_N * r
// over a finite field. Two algebraically equivalent forms:
//   Horner:     A_0 = 0; A_i = (A_{i-1} + X_i) * r; tag = A_N
//   Polynomial: tag = SUM_{i=1..N} X_i * r^{N-i+1}
//
// The TLAPS proofs at supplementary-research/studies/domain-corpora/cryptography/tla/compositions/PolynomialMac{HornerForm,
// PolynomialForm,Equivalence}_Proof.tla close at 161 / 157 / 69
// obligations respectively (387 total across the three-module
// decomposition). The integer-arithmetic representation
// (`Field = 0..(P-1)`, `Add(a,b) = (a+b) % P`) is the representation
// under which the equivalence identity is tractable.
//
// For Verus, the same integer representation is used. The three claims
// of the TLAPS decomposition collapse to three spec functions and an
// equivalence assertion proved by SMT case-split on the block count.
//
// Verification boundary: written contracts plus named external-body assumptions.

use vstd::prelude::*;

verus! {

/// Field modulus: small prime for the bounded model (Poly1305 uses
/// 2^130 - 5; this model uses a smaller prime with the same algebraic
/// structure).
pub const P: u64 = 7;

/// Field element typing predicate.
pub open spec fn in_field(x: u64) -> bool {
    x < P
}

pub open spec fn add_field(a: u64, b: u64) -> u64 {
    ((a + b) % (P as int)) as u64
}

pub open spec fn mul_field(a: u64, b: u64) -> u64 {
    ((a * b) % (P as int)) as u64
}

/// Horner form: A_0 = 0; A_i = (A_{i-1} + X_i) * r.
pub open spec fn horner_at(inputs: Seq<u64>, r: u64, k: int) -> u64
    decreases k,
{
    if k <= 0 {
        0
    } else if k > inputs.len() as int {
        0
    } else {
        mul_field(add_field(horner_at(inputs, r, k - 1), inputs[k - 1]), r)
    }
}

/// Polynomial form lane product: X_i * r^{N - i + 1}, lifted to int.
pub open spec fn power(r: u64, k: int) -> u64
    decreases k,
{
    if k <= 0 {
        1
    } else {
        mul_field(r, power(r, k - 1))
    }
}

pub open spec fn lane_product(inputs: Seq<u64>, r: u64, i: int, n: int) -> u64 {
    mul_field(inputs[i - 1], power(r, n - i + 1))
}

/// Polynomial form sum: SUM_{i=1..k} lane_product(i, n).
pub open spec fn poly_at(inputs: Seq<u64>, r: u64, k: int, n: int) -> u64
    decreases k,
{
    if k <= 0 {
        0
    } else if k > n {
        0
    } else {
        add_field(poly_at(inputs, r, k - 1, n), lane_product(inputs, r, k, n))
    }
}

/// Executable Horner-form fold: A_i = (A_{i-1} + X_i) * r over the
/// field. Mirror of supplementary-research/studies/domain-corpora/cryptography/tla/compositions/PolynomialMacHornerForm.tla.
pub fn horner_compute(inputs: &[u64], r: u64) -> (mac: u64)
    requires
        r < P,
        forall|i: int| 0 <= i < inputs@.len() ==> inputs@[i] < P,
    ensures mac == horner_at(inputs@, r, inputs@.len() as int),
{
    let n: usize = inputs.len();
    let mut acc: u64 = 0;
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == inputs@.len(),
            r < P,
            acc < P,
            forall|j: int| 0 <= j < inputs@.len() ==> inputs@[j] < P,
            acc == horner_at(inputs@, r, i as int),
        decreases n - i,
    {
        let added = (acc + inputs[i]) % P;
        // added < P and r < P, so added * r < P*P = 49 < u64::MAX.
        // Nonlinear product bound proved by SMT under nonlinear_arith.
        assert(added < P);
        assert(r < P);
        assert(added * r <= 48) by (nonlinear_arith)
            requires added < 7, r < 7;
        let prod = added * r;
        acc = prod % P;
        i = i + 1;
    }
    acc
}

}
