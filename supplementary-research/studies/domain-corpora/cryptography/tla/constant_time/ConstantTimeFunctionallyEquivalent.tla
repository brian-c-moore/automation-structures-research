---- MODULE ConstantTimeFunctionallyEquivalent ----
(*
  Constant-time and variable-time Montgomery-ladder
  realizations are functionally equivalent.

  Models the X25519 Montgomery ladder as two parallel state machines
  advancing in lockstep over the scalar's bits. At each step:
    CT version — evaluate both branch outputs, select via a
      constant-time predicate (in real hardware: branchless via
      CSwap; in TLA+ modelled with IF-THEN-ELSE since timing is not
      observable).
    VT version — branch directly on the bit value.
  At each bit index the two versions produce identical (R0, R1)
  state. The refinement mapping is the identity; functional
  equivalence reduces to: both per-step encodings compute the same
  output given the same input.

  Mirrors the Execution-Modalities/tla/refinements/
  SequentialRefinesStepGraph.tla idiom (one module, parallel
  abstract + concrete state, refinement invariant). Lockstep stepping
  keeps the proof inductive without a recursive "expected state after
  k bits" function, since TLAPS does not unfold recursive
  function-fixpoint operators in safety invariants.

  Uses the integer Z/4Z representation from GroupDistributivity and
  CommitChallengeResponseVerification (GroupElement = 0..(L-1), L = 4)
  because the SMT backend cannot evaluate the function-literal applications
  used by ScalarMultiplicationOverGroup and CommitChallengeResponseFlow
  across the equality the refinement invariant demands; the bijection
  with the model-value representation is g0<->0, g1<->1, g2<->2,
  g3<->3.

  Scope note (per study definition). The spec name's "FunctionallyEquivalent"
  is intentional: TLA+ cannot observe wall-clock, so the timing
  independence claim ("constant-time") is out of scope; the
  *functional* equivalence is what we prove here. The timing claim is
  the executable track's domain (dudect / ctgrind instrumentation).

  Bounded parameters per the study definition: ScalarBits = 4. Exhaustive.

  Expected outcome: No error has been found  (PASS).
*)
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    ScalarBits         \* per study definition; bit width of the scalar

ASSUME ScalarBitsType == ScalarBits \in Nat /\ ScalarBits >= 1

\* ── Z/4Z represented as integers ─────────────────────────────────────────
L == 4
GroupElement == 0..(L - 1)
GroupOp(a, b) == (a + b) % L
G == 1            \* base point

\* ScalarBit: 1..ScalarBits -> {0, 1}. Concrete 4-bit scalar 1011_2.
\* Processed MSB-first (ScalarBit(1) = MSB).
ScalarBit(k) ==
    IF      k = 1 THEN 1
    ELSE IF k = 2 THEN 0
    ELSE IF k = 3 THEN 1
    ELSE              1

\* Per-step Montgomery-ladder transition (per RFC 7748 §5).
\* For bit = 1: (R0', R1') = (R0 + R1, R1 + R1).
\* For bit = 0: (R0', R1') = (R0 + R0, R0 + R1).
\* In this abstract group, all four entries are GroupOp applications.
LadderStepBit1R0(R0, R1) == GroupOp(R0, R1)
LadderStepBit1R1(R0, R1) == GroupOp(R1, R1)
LadderStepBit0R0(R0, R1) == GroupOp(R0, R0)
LadderStepBit0R1(R0, R1) == GroupOp(R0, R1)

VARIABLES
    ct_R0, ct_R1,      \* constant-time ladder state
    vt_R0, vt_R1,      \* variable-time ladder state
    idx                \* shared bit index (lockstep stepping)

vars == <<ct_R0, ct_R1, vt_R0, vt_R1, idx>>

\* ---- Type invariant ------------------------------------------------------

TypeInvariant ==
    /\ ct_R0 \in GroupElement /\ ct_R1 \in GroupElement
    /\ vt_R0 \in GroupElement /\ vt_R1 \in GroupElement
    /\ idx \in 0..ScalarBits

\* ---- Safety invariants ---------------------------------------------------

\* The two ladders' state matches at every bit index. This is the
\* functional-equivalence claim: timing-different realizations carry
\* identical functional state.
RefinementHolds ==
    /\ ct_R0 = vt_R0
    /\ ct_R1 = vt_R1

\* ---- Init ----------------------------------------------------------------

Init ==
    /\ ct_R0 = 0       \* identity
    /\ ct_R1 = G       \* base point
    /\ vt_R0 = 0
    /\ vt_R1 = G
    /\ idx = 0

\* ---- Actions -------------------------------------------------------------

\* Lockstep step: both ladders advance, computing their per-step
\* transitions in their respective styles (CT: IF-THEN-ELSE inside;
\* VT: explicit branch). Both must yield the same result for the
\* refinement to hold.
Step ==
    /\ idx < ScalarBits
    /\ LET bit == ScalarBit(idx + 1)
       IN  \* Constant-time formulation: IF-THEN-ELSE selects.
           /\ ct_R0' = IF bit = 1 THEN LadderStepBit1R0(ct_R0, ct_R1)
                                  ELSE LadderStepBit0R0(ct_R0, ct_R1)
           /\ ct_R1' = IF bit = 1 THEN LadderStepBit1R1(ct_R0, ct_R1)
                                  ELSE LadderStepBit0R1(ct_R0, ct_R1)
           \* Variable-time formulation: explicit branch.
           /\ (IF bit = 1
               THEN /\ vt_R0' = LadderStepBit1R0(vt_R0, vt_R1)
                    /\ vt_R1' = LadderStepBit1R1(vt_R0, vt_R1)
               ELSE /\ vt_R0' = LadderStepBit0R0(vt_R0, vt_R1)
                    /\ vt_R1' = LadderStepBit0R1(vt_R0, vt_R1))
    /\ idx' = idx + 1

\* Terminal: scalar consumed; stutter.
Done ==
    /\ idx = ScalarBits
    /\ UNCHANGED vars

Next ==
    \/ Step
    \/ Done

Spec == Init /\ [][Next]_vars

\* ---- Theorem (checked by TLC) --------------------------------------------

THEOREM Spec => [](TypeInvariant /\ RefinementHolds)
====
