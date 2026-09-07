---- MODULE ConstantTimeFunctionallyEquivalent_Proof ----
(***************************************************************************
  TLAPS proof of safety for ConstantTimeFunctionallyEquivalent.

  Discharges the THEOREM declared in
  ConstantTimeFunctionallyEquivalent.tla:
      Spec => [](TypeInvariant /\ RefinementHolds)

  Inductive strengthening: none beyond the two cfg invariants. With
  lockstep stepping, the refinement claim `ct_R0 = vt_R0 /\ ct_R1 =
  vt_R1` is itself inductive: per step, both ladders apply the same
  per-step transition (CT's IF-THEN-ELSE selects the same branch as
  VT's explicit branch), so equal pre-states yield equal post-states.

  This proof module artifact per the TLA+ study contract
  Mirror of SequentialRefinesStepGraph_Proof.tla refinement pattern
  (one-module abstract+concrete + identity refinement mapping).
 ***************************************************************************)
EXTENDS ConstantTimeFunctionallyEquivalent, Naturals, Sequences, FiniteSets, TLAPS

ASSUME ScalarBitsAss == ScalarBits \in Nat /\ ScalarBits >= 1

\* Helper lemmas.
LEMMA GroupOpType ==
    \A a \in GroupElement, b \in GroupElement : GroupOp(a, b) \in GroupElement
  BY DEF GroupOp, GroupElement, L

LEMMA GType == G \in GroupElement
  BY DEF G, GroupElement, L

LEMMA ScalarBitDomain ==
    \A k \in 1..ScalarBits : ScalarBit(k) \in {0, 1}
  BY DEF ScalarBit

\* Inductive invariant.
Inv == TypeInvariant /\ RefinementHolds

(*-------------------------------------------------------------------------*)
(* Lemma: Init establishes the inductive invariant.                        *)
(*-------------------------------------------------------------------------*)
LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv
    OBVIOUS
  <1>1. TypeInvariant
    BY GType, ScalarBitsAss DEF Init, TypeInvariant, GroupElement, L
  <1>2. RefinementHolds
    BY DEF Init, RefinementHolds
  <1> QED  BY <1>1, <1>2 DEF Inv

(*-------------------------------------------------------------------------*)
(* Lemma: every Next step preserves the inductive invariant.               *)
(*-------------------------------------------------------------------------*)
LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <1> USE DEF Inv, TypeInvariant, RefinementHolds
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF vars
  <1>A. CASE Step
    <2>a. idx < ScalarBits                                BY <1>A DEF Step
    <2>b. idx' = idx + 1                                  BY <1>A DEF Step
    <2>c. idx + 1 \in 1..ScalarBits                       BY <2>a, ScalarBitsAss
    <2>d. ScalarBit(idx + 1) \in {0, 1}                   BY <2>c, ScalarBitDomain
    <2>e. ct_R0 \in GroupElement /\ ct_R1 \in GroupElement OBVIOUS
    <2>f. vt_R0 \in GroupElement /\ vt_R1 \in GroupElement OBVIOUS
    <2>g. ct_R0 = vt_R0 /\ ct_R1 = vt_R1                  OBVIOUS
    \* CT transitions.
    <2>h. ct_R0' = IF ScalarBit(idx + 1) = 1
                   THEN LadderStepBit1R0(ct_R0, ct_R1)
                   ELSE LadderStepBit0R0(ct_R0, ct_R1)
      BY <1>A DEF Step
    <2>i. ct_R1' = IF ScalarBit(idx + 1) = 1
                   THEN LadderStepBit1R1(ct_R0, ct_R1)
                   ELSE LadderStepBit0R1(ct_R0, ct_R1)
      BY <1>A DEF Step
    \* VT transitions.
    <2>j. \/ (/\ ScalarBit(idx + 1) = 1
              /\ vt_R0' = LadderStepBit1R0(vt_R0, vt_R1)
              /\ vt_R1' = LadderStepBit1R1(vt_R0, vt_R1))
          \/ (/\ ScalarBit(idx + 1) /= 1
              /\ vt_R0' = LadderStepBit0R0(vt_R0, vt_R1)
              /\ vt_R1' = LadderStepBit0R1(vt_R0, vt_R1))
      BY <1>A DEF Step
    \* Case split on the bit.
    <2>B1. CASE ScalarBit(idx + 1) = 1
      <3>1. ct_R0' = LadderStepBit1R0(ct_R0, ct_R1)
        BY <2>B1, <2>h
      <3>2. ct_R1' = LadderStepBit1R1(ct_R0, ct_R1)
        BY <2>B1, <2>i
      <3>3. vt_R0' = LadderStepBit1R0(vt_R0, vt_R1)
        BY <2>B1, <2>j
      <3>4. vt_R1' = LadderStepBit1R1(vt_R0, vt_R1)
        BY <2>B1, <2>j
      <3>5. ct_R0' \in GroupElement
        BY <3>1, <2>e, GroupOpType DEF LadderStepBit1R0
      <3>6. ct_R1' \in GroupElement
        BY <3>2, <2>e, GroupOpType DEF LadderStepBit1R1
      <3>7. vt_R0' \in GroupElement
        BY <3>3, <2>f, GroupOpType DEF LadderStepBit1R0
      <3>8. vt_R1' \in GroupElement
        BY <3>4, <2>f, GroupOpType DEF LadderStepBit1R1
      <3>9. ct_R0' = vt_R0'
        BY <3>1, <3>3, <2>g DEF LadderStepBit1R0
      <3>10. ct_R1' = vt_R1'
        BY <3>2, <3>4, <2>g DEF LadderStepBit1R1
      <3>11. TypeInvariant'
        BY <3>5, <3>6, <3>7, <3>8, <2>b, <2>a, ScalarBitsAss
      <3>12. RefinementHolds'
        BY <3>9, <3>10
      <3> QED  BY <3>11, <3>12
    <2>B0. CASE ScalarBit(idx + 1) /= 1
      <3>1. ct_R0' = LadderStepBit0R0(ct_R0, ct_R1)
        BY <2>B0, <2>h
      <3>2. ct_R1' = LadderStepBit0R1(ct_R0, ct_R1)
        BY <2>B0, <2>i
      <3>3. vt_R0' = LadderStepBit0R0(vt_R0, vt_R1)
        BY <2>B0, <2>j
      <3>4. vt_R1' = LadderStepBit0R1(vt_R0, vt_R1)
        BY <2>B0, <2>j
      <3>5. ct_R0' \in GroupElement
        BY <3>1, <2>e, GroupOpType DEF LadderStepBit0R0
      <3>6. ct_R1' \in GroupElement
        BY <3>2, <2>e, GroupOpType DEF LadderStepBit0R1
      <3>7. vt_R0' \in GroupElement
        BY <3>3, <2>f, GroupOpType DEF LadderStepBit0R0
      <3>8. vt_R1' \in GroupElement
        BY <3>4, <2>f, GroupOpType DEF LadderStepBit0R1
      <3>9. ct_R0' = vt_R0'
        BY <3>1, <3>3, <2>g DEF LadderStepBit0R0
      <3>10. ct_R1' = vt_R1'
        BY <3>2, <3>4, <2>g DEF LadderStepBit0R1
      <3>11. TypeInvariant'
        BY <3>5, <3>6, <3>7, <3>8, <2>b, <2>a, ScalarBitsAss
      <3>12. RefinementHolds'
        BY <3>9, <3>10
      <3> QED  BY <3>11, <3>12
    <2> QED  BY <2>B1, <2>B0, <2>d
  <1>B. CASE Done
    BY <1>B DEF Done, vars
  <1>C. CASE Next
    BY <1>C, <1>A, <1>B DEF Next
  <1> QED  BY <1>0, <1>C

(*-------------------------------------------------------------------------*)
(* Main safety theorem.                                                    *)
(*-------------------------------------------------------------------------*)
THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv                       BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'        BY NextInv
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

THEOREM TypeInvariantSafety == Spec => []TypeInvariant
  BY Safety, PTL DEF Inv

THEOREM RefinementHoldsSafety == Spec => []RefinementHolds
  BY Safety, PTL DEF Inv

====
