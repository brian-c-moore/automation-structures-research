---- MODULE GroupDistributivity ----
(*
  Group distributivity bridge for the
  CommitChallengeResponse decomposition.

  Establishes two algebraic identities over the Z/4Z group used by
  ScalarMultiplicationOverGroup, CommitChallengeResponseFlow and
  CommitChallengeResponseVerification:

    Distributivity:
        ScalarMult(ScalarAdd(a, b), P) =
          GroupOp(ScalarMult(a, P), ScalarMult(b, P))
        for all a, b in ScalarValue, P in GroupElement.

    ScalarMultAssociativity:
        ScalarMult(ScalarMul(a, b), P) =
          ScalarMult(a, ScalarMult(b, P))
        for all a, b in ScalarValue, P in GroupElement.

  Together these underpin the verification equation s * G = R + c * A
  proved in CommitChallengeResponseVerification.

  Modeling note. ScalarMultiplicationOverGroup and
  CommitChallengeResponseFlow represent the 4-element cyclic group with the
  four model values {g0, g1, g2, g3}; that works for chain-correctness
  (ScalarMultiplicationOverGroup's RoundFnType idiom) where the proof
  obligation is membership, not equality. The algebraic-identity proof here
  instead needs SMT to evaluate `ScalarMult(k, P)` to a specific group
  element on each side of the identity, and the TLAPS SMT backend does not
  unfold function-literal applications across case-splits. So this bridge
  module follows PolynomialMacEquivalence's integer-arithmetic pattern:
  GroupElement = 0..(L-1), all four operators are integer-arithmetic
  OPERATORS (not function literals), and the identities reduce to
  mod-L arithmetic equalities that SMT handles directly. The bijection
  with the model-value representation is g0 <-> 0, g1 <-> 1, g2 <->
  2, g3 <-> 3; the algebraic identities proved here apply to either
  representation since Z/4Z is determined by its operation table.

  As a bridge module it redefines the operators it needs locally; the
  representation choice is internal to this module.

  Expected outcome: No error has been found  (PASS).
*)
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    BitsPerScalar      \* per study definition; consistent with the sibling modules

ASSUME BitsPerScalarType == BitsPerScalar \in Nat /\ BitsPerScalar = 4

\* ── Z/4Z as integers 0..3 (mirror of PolynomialMacHornerForm's GF(P) idiom) ──
L == 4
GroupElement == 0..(L - 1)
GroupIdentity == 0
ScalarValue == 0..(L - 1)
GroupOp(a, b) == (a + b) % L
ScalarAdd(a, b) == (a + b) % L
ScalarMul(a, b) == (a * b) % L
ScalarMult(k, P) == (k * P) % L

\* ── Static state machine (mirror of PolynomialMacEquivalence) ────────────
VARIABLES proven
vars == <<proven>>

Init == proven = TRUE
Next == UNCHANGED proven
Spec == Init /\ [][Next]_vars

\* Type invariant (trivial).
TypeInvariant == proven = TRUE

\* Algebraic identity 1: scalar-add distributes over scalar-mult.
Distributivity ==
    \A a \in ScalarValue, b \in ScalarValue, P \in GroupElement :
        ScalarMult(ScalarAdd(a, b), P) =
            GroupOp(ScalarMult(a, P), ScalarMult(b, P))

\* Algebraic identity 2: scalar-mul associates with scalar-mult.
ScalarMultAssociativity ==
    \A a \in ScalarValue, b \in ScalarValue, P \in GroupElement :
        ScalarMult(ScalarMul(a, b), P) =
            ScalarMult(a, ScalarMult(b, P))

THEOREM Spec => [](TypeInvariant /\ Distributivity /\ ScalarMultAssociativity)
====
