---- MODULE PolynomialMacPolynomialForm ----
(*
  Polynomial-MAC accumulation, polynomial form.

  Sibling of PolynomialMacHornerForm. The same MAC value is computed via a
  precomputed power table r^1..r^N and per-lane multiplication followed
  by Reduction (sum). DAG ordering across lanes: lane k can be computed
  independently of lane k' since their inputs are disjoint.

  Pattern.  Compute lane_k = X_k * r^(N - k + 1) for k in 1..N; sum lane
  values to obtain the polynomial-evaluation result
      M(r) = X_1 * r^N + X_2 * r^(N-1) + ... + X_N * r.

  Canonical examples: GHASH (in AES-GCM, SIMD-optimized), Poly1305
  (with precomputed r-powers in vectorized implementations).

  Build requirements demonstrated: ResourceRegistry (running sum +
    lane progress) + TraversalEngine (over lanes; per-lane independent
    so the order doesn't matter) + ActuationPass (per-lane multiply) +
    Reduction (sum of lane products into running_sum).

  Safety claims:
    PartialSumCorrect — running_sum after lane_idx lanes equals the sum
      of X_k * r^(N - k + 1) for k in 1..lane_idx.

  Bounded parameters per the study definition: Blocks = 4, Field = GF(7).
  Same parameters as PolynomialMacHornerForm so PolynomialMacEquivalence can
  compare results directly.

  Expected outcome: No error has been found  (PASS).
*)
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    P,             \* field modulus (prime); same as PolynomialMacHornerForm
    R,             \* evaluation point r; same as PolynomialMacHornerForm
    Blocks         \* number of input blocks; same as PolynomialMacHornerForm

ASSUME PType      == P \in Nat /\ P >= 5
ASSUME RType      == R \in Nat /\ R < P
ASSUME BlocksType == Blocks \in Nat /\ Blocks >= 1 /\ Blocks <= 4

\* ── Fixed topology ───────────────────────────────────────────────────────
Field == 0..(P - 1)
FieldZero == 0

Add(a, b) == (a + b) % P
Mul(a, b) == (a * b) % P

\* Same InputBlock as PolynomialMacHornerForm, so the equivalence checked in
\* PolynomialMacEquivalence is meaningful.
InputBlock ==
    [k \in 1..Blocks |->
        IF      k = 1 THEN 1
        ELSE IF k = 2 THEN 2
        ELSE IF k = 3 THEN 3
        ELSE              4]

\* Precomputed power table: PowerAt(k) = R^k mod P.  Unrolled for Blocks <= 4
\* to keep the operator non-recursive.
PowerAt(k) ==
    IF      k = 1 THEN R
    ELSE IF k = 2 THEN Mul(R, R)
    ELSE IF k = 3 THEN Mul(Mul(R, R), R)
    ELSE                 Mul(Mul(Mul(R, R), R), R)

\* LaneProduct(i) = X_i * r^(N - i + 1).  The i-th lane's contribution to
\* the polynomial-evaluation sum.
LaneProduct(i) == Mul(InputBlock[i], PowerAt(Blocks - i + 1))

VARIABLES
    lane_idx,      \* 0..Blocks (number of lanes processed)
    running_sum    \* Field — sum of lane products processed so far

vars == <<lane_idx, running_sum>>

\* ---- Type invariant ------------------------------------------------------

TypeInvariant ==
    /\ lane_idx \in 0..Blocks
    /\ running_sum \in Field

\* ---- Safety invariants ---------------------------------------------------

\* The expected running_sum after k lanes have been processed. Unrolled
\* explicitly for Blocks <= 4 to keep the operator non-recursive: TLAPS does
\* not unfold recursive function fixpoints, and TLC cannot enumerate
\* Seq(Field).
ExpectedSumAt(k) ==
    IF      k = 0 THEN FieldZero
    ELSE IF k = 1 THEN Add(FieldZero, LaneProduct(1))
    ELSE IF k = 2 THEN Add(Add(FieldZero, LaneProduct(1)), LaneProduct(2))
    ELSE IF k = 3 THEN Add(Add(Add(FieldZero, LaneProduct(1)), LaneProduct(2)),
                            LaneProduct(3))
    ELSE              Add(Add(Add(Add(FieldZero, LaneProduct(1)), LaneProduct(2)),
                                LaneProduct(3)), LaneProduct(4))

\* After lane_idx lanes, running_sum equals the expected partial sum.
PartialSumCorrect == running_sum = ExpectedSumAt(lane_idx)

\* ---- Init ----------------------------------------------------------------

Init ==
    /\ lane_idx = 0
    /\ running_sum = FieldZero

\* ---- Actions -------------------------------------------------------------

ComputeAndAddLane ==
    /\ lane_idx < Blocks
    /\ running_sum' = Add(running_sum, LaneProduct(lane_idx + 1))
    /\ lane_idx' = lane_idx + 1

Done ==
    /\ lane_idx = Blocks
    /\ UNCHANGED vars

Next ==
    \/ ComputeAndAddLane
    \/ Done

Spec == Init /\ [][Next]_vars

\* ---- Theorem (checked by TLC) --------------------------------------------

THEOREM Spec => [](TypeInvariant /\ PartialSumCorrect)
====
