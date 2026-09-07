---- MODULE HardwareAcceleratedRefinesBase_Proof ----
(***************************************************************************
  TLAPS proof of safety for HardwareAcceleratedRefinesBase.

  Discharges the THEOREM declared in HardwareAcceleratedRefinesBase.tla:
      Spec => [](TypeInvariant /\ RefinementHolds)

  Inductive strengthening: none. With lockstep stepping, both
  implementations apply the same RoundFn per round to identical pre-
  states; equality is preserved trivially.

  This proof module checks the written hardware-acceleration relation.
  Mirror of BitslicedRefinesBase_Proof.tla.
 ***************************************************************************)
EXTENDS HardwareAcceleratedRefinesBase, Naturals, Sequences, FiniteSets, TLAPS

ASSUME RoundsAss == Rounds \in Nat /\ Rounds >= 1 /\ Rounds <= 4
ASSUME BitsAss   == Bits \in Nat /\ Bits >= 1 /\ Bits <= 4

LEMMA RoundFnType ==
    \A s \in StateValue, r \in Nat : RoundFn(s, r) \in StateValue
  BY MConcrete DEF RoundFn, StateValue, M

Inv == TypeInvariant /\ RefinementHolds

LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv
    OBVIOUS
  <1>1. TypeInvariant
    BY RoundsAss, BitsAss, MConcrete, RoundsConcrete
       DEF Init, TypeInvariant, StateValue, M, Init0
  <1>2. RefinementHolds
    BY DEF Init, RefinementHolds
  <1> QED  BY <1>1, <1>2 DEF Inv

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <1> USE DEF Inv, TypeInvariant, RefinementHolds
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF vars
  <1>A. CASE Step
    <2>a. rnd < Rounds                                    BY <1>A DEF Step
    <2>b. rnd' = rnd + 1                                  BY <1>A DEF Step
    <2>c. base_state' = RoundFn(base_state, rnd + 1)      BY <1>A DEF Step
    <2>d. hw_state' = RoundFn(hw_state, rnd + 1)          BY <1>A DEF Step
    <2>e. base_state \in StateValue                       OBVIOUS
    <2>f. hw_state \in StateValue                         OBVIOUS
    <2>g. rnd + 1 \in Nat                                 BY <2>a, RoundsAss
    <2>h. base_state' \in StateValue                      BY <2>c, <2>e, <2>g, RoundFnType
    <2>i. hw_state' \in StateValue                        BY <2>d, <2>f, <2>g, RoundFnType
    <2>j. base_state = hw_state                           OBVIOUS
    <2>1. TypeInvariant'
      BY <2>a, <2>b, <2>h, <2>i, RoundsAss
    <2>2. RefinementHolds'
      BY <2>c, <2>d, <2>j
    <2> QED  BY <2>1, <2>2
  <1>B. CASE Done
    BY <1>B DEF Done, vars
  <1>C. CASE Next
    BY <1>C, <1>A, <1>B DEF Next
  <1> QED  BY <1>0, <1>C

THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv                       BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'        BY NextInv
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

THEOREM TypeInvariantSafety == Spec => []TypeInvariant
  BY Safety, PTL DEF Inv

THEOREM RefinementHoldsSafety == Spec => []RefinementHolds
  BY Safety, PTL DEF Inv

====
