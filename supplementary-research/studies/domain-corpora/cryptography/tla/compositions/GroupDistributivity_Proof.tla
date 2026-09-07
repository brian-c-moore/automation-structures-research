---- MODULE GroupDistributivity_Proof ----
(***************************************************************************
  TLAPS proof of safety for GroupDistributivity, the algebraic-identity
  bridge between CommitChallengeResponseFlow and
  CommitChallengeResponseVerification.

  Discharges the THEOREM declared in GroupDistributivity.tla:
      Spec => [](TypeInvariant /\ Distributivity /\ ScalarMultAssociativity)

  Both identities reduce to mod-L arithmetic over integers (the bridge
  module's representation choice per the .tla header note). SMT handles
  the mod-arithmetic equalities directly with operator-definition
  unfolding; no case-split is needed (in contrast to the model-value
  representation where SMT cannot unfold function-literal applications
  across case-splits). Init and Next are trivial (the state is just
  `proven = TRUE`).

  This proof module covers the algebraic-identity piece of the
  decomposition. It mirrors PolynomialMacEquivalence_Proof.tla's
  static-identity proof pattern.
 ***************************************************************************)
EXTENDS GroupDistributivity, Naturals, Sequences, FiniteSets, TLAPS

ASSUME BitsPerScalarAss == BitsPerScalar \in Nat /\ BitsPerScalar = 4

\* The two identities are mod-L arithmetic equalities. SMT discharges
\* each by unfolding the operator definitions; no case-split required.
LEMMA DistributivityStatic == Distributivity
  BY DEF Distributivity, ScalarMult, GroupOp, ScalarAdd,
         ScalarValue, GroupElement, L

LEMMA ScalarMultAssociativityStatic == ScalarMultAssociativity
  BY DEF ScalarMultAssociativity, ScalarMult, ScalarMul,
         ScalarValue, GroupElement, L

\* Inductive invariant.
Inv == TypeInvariant /\ Distributivity /\ ScalarMultAssociativity

LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv
    OBVIOUS
  <1>1. TypeInvariant
    BY DEF Init, TypeInvariant
  <1>2. Distributivity
    BY DistributivityStatic
  <1>3. ScalarMultAssociativity
    BY ScalarMultAssociativityStatic
  <1> QED  BY <1>1, <1>2, <1>3 DEF Inv

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <1> USE DEF Inv, TypeInvariant
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF vars
  <1>1. CASE Next
    \* Next is UNCHANGED proven; identities are state-independent.
    <2>1. TypeInvariant'
      BY <1>1 DEF Next
    <2>2. Distributivity'
      BY DistributivityStatic DEF Distributivity
    <2>3. ScalarMultAssociativity'
      BY ScalarMultAssociativityStatic DEF ScalarMultAssociativity
    <2> QED  BY <2>1, <2>2, <2>3
  <1> QED  BY <1>0, <1>1

THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv                       BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'        BY NextInv
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

THEOREM TypeInvariantSafety == Spec => []TypeInvariant
  BY Safety, PTL DEF Inv

THEOREM DistributivitySafety == Spec => []Distributivity
  BY Safety, PTL DEF Inv

THEOREM ScalarMultAssociativitySafety == Spec => []ScalarMultAssociativity
  BY Safety, PTL DEF Inv

====
