---- MODULE PolynomialMacEquivalence_Proof ----
(***************************************************************************
  TLAPS proof of safety for PolynomialMacEquivalence, the equivalence bridge
  between the Horner-form and polynomial-form polynomial-MAC accumulators.

  Discharges the THEOREM declared in PolynomialMacEquivalence.tla:
      Spec => [](TypeInvariant /\ EquivalenceHolds)

  The substantive content is in EquivalenceHolds, a state-independent
  closed equality for P = 7, R = 3, and Blocks = 4. This module does not
  claim the generic algebraic identity for other parameter values. Init and Next
  are trivial (the state is just `proven = TRUE`, with `Next ==
  UNCHANGED proven`); InitInv and NextInv are correspondingly trivial.

  This proof module per the written two-form decomposition.
 ***************************************************************************)
EXTENDS PolynomialMacEquivalence, Naturals, Sequences, FiniteSets, TLAPS

\* The configured-instance identity reduces to a closed modular-arithmetic
\* equality after the model and operator definitions are unfolded.
LEMMA EquivalenceStatic == HornerAt(Blocks) = PolyAt(Blocks)
  BY PConcrete, RConcrete, BlocksConcrete
     DEF HornerAt, PolyAt, LaneProduct, PowerAt, InputBlock,
         Add, Mul, FieldZero

\* Inductive invariant.
Inv == TypeInvariant /\ EquivalenceHolds

LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv
    OBVIOUS
  <1>1. TypeInvariant
    BY DEF Init, TypeInvariant
  <1>2. EquivalenceHolds
    BY EquivalenceStatic DEF EquivalenceHolds
  <1> QED  BY <1>1, <1>2 DEF Inv

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <1> USE DEF Inv, TypeInvariant, EquivalenceHolds
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF vars
  <1>1. CASE Next
    \* Next is UNCHANGED proven, but the EquivalenceHolds invariant is
    \* state-independent (uses only CONSTANTS), so it's preserved.
    <2>1. TypeInvariant'
      BY <1>1 DEF Next
    <2>2. EquivalenceHolds'
      BY EquivalenceStatic DEF EquivalenceHolds
    <2> QED  BY <2>1, <2>2
  <1> QED  BY <1>0, <1>1

THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv                       BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'        BY NextInv
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

THEOREM TypeInvariantSafety == Spec => []TypeInvariant
  BY Safety, PTL DEF Inv

THEOREM EquivalenceHoldsSafety == Spec => []EquivalenceHolds
  BY Safety, PTL DEF Inv

====
