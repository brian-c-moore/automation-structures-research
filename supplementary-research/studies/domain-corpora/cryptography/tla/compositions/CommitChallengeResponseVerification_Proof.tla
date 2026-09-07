---- MODULE CommitChallengeResponseVerification_Proof ----
(***************************************************************************
  TLAPS proof of safety for CommitChallengeResponseVerification, the
  verification-equation bridge for the three-part Ed25519 decomposition.

  Discharges the THEOREM declared in CommitChallengeResponseVerification.tla:
      Spec => [](TypeInvariant /\ VerificationEquationHolds)

  The verification equation is a single concrete equality in the bridge's
  integer representation: LHS = (1 * 1) % 4 = 1; RHS = (3 + (1 * 2) % 4) % 4
  = (3 + 2) % 4 = 1. SMT discharges by unfolding the operator definitions
  and reducing the mod-arithmetic. No case-split required.

  This proof module covers the bridge piece of the decomposition. It
  mirrors PolynomialMacEquivalence_Proof.tla's static-identity bridge
  pattern.
 ***************************************************************************)
EXTENDS CommitChallengeResponseVerification, Naturals, Sequences, FiniteSets, TLAPS

ASSUME BitsPerScalarAss == BitsPerScalar \in Nat /\ BitsPerScalar = 4

\* The verification equation reduces to mod-4 arithmetic with all values
\* concrete.
LEMMA VerificationStatic == VerificationEquationHolds
  BY DEF VerificationEquationHolds, s_scalar, c_scalar, R_point,
         G, A, M_hash, a_secret, r_nonce,
         ScalarMult, GroupOp, Hash, ScalarAdd, ScalarMul,
         GroupElement, ScalarValue, L

\* Inductive invariant.
Inv == TypeInvariant /\ VerificationEquationHolds

LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv
    OBVIOUS
  <1>1. TypeInvariant
    BY DEF Init, TypeInvariant
  <1>2. VerificationEquationHolds
    BY VerificationStatic
  <1> QED  BY <1>1, <1>2 DEF Inv

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <1> USE DEF Inv, TypeInvariant
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF vars
  <1>1. CASE Next
    \* Next is UNCHANGED proven; the verification equation is
    \* state-independent (uses only CONSTANTS / operators).
    <2>1. TypeInvariant'
      BY <1>1 DEF Next
    <2>2. VerificationEquationHolds'
      BY VerificationStatic DEF VerificationEquationHolds
    <2> QED  BY <2>1, <2>2
  <1> QED  BY <1>0, <1>1

THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv                       BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'        BY NextInv
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

THEOREM TypeInvariantSafety == Spec => []TypeInvariant
  BY Safety, PTL DEF Inv

THEOREM VerificationEquationHoldsSafety == Spec => []VerificationEquationHolds
  BY Safety, PTL DEF Inv

====
