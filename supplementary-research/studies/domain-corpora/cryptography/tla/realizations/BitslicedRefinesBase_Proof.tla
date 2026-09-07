---- MODULE BitslicedRefinesBase_Proof ----
(***************************************************************************
  TLAPS proof of safety for BitslicedRefinesBase.

  Discharges the THEOREM declared in BitslicedRefinesBase.tla:
      Spec => [](TypeInvariant /\ RefinementHolds)

  Inductive strengthening: none beyond the two cfg invariants. With
  lockstep stepping, the refinement holds per step by construction:
  both base and bitsliced apply RoundFn(_, rnd+1) componentwise, and
  the pre-state has base_states[k] = bitsliced_state[k] for all k.

  This proof module checks the written bitsliced relation.
  Mirror of ConstantTimeFunctionallyEquivalent_Proof.tla
  lockstep-refinement pattern.
 ***************************************************************************)
EXTENDS BitslicedRefinesBase, Naturals, Sequences, FiniteSets, TLAPS

ASSUME NAss    == N \in Nat /\ N >= 1 /\ N <= 4
ASSUME BitsAss == Bits \in Nat /\ Bits >= 1 /\ Bits <= 4

\* Helper: RoundFn closure.
LEMMA RoundFnType ==
    \A s \in StateValue, r \in Nat : RoundFn(s, r) \in StateValue
  BY MConcrete DEF RoundFn, StateValue, M

\* Inductive invariant.
Inv == TypeInvariant /\ RefinementHolds

(*-------------------------------------------------------------------------*)
(* Lemma: Init establishes the inductive invariant.                        *)
(*-------------------------------------------------------------------------*)
LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv
    OBVIOUS
  <1>1. TypeInvariant
    BY NAss, BitsAss, MConcrete, NConcrete
       DEF Init, TypeInvariant, InputSlot, StateValue, M,
           Init0, Rounds
  <1>2. RefinementHolds
    BY DEF Init, RefinementHolds, InputSlot
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
    <2>a. rnd < Rounds                                    BY <1>A DEF Step
    <2>b. rnd' = rnd + 1                                  BY <1>A DEF Step
    <2>c. base_states' = [k \in InputSlot |-> RoundFn(base_states[k], rnd + 1)]
      BY <1>A DEF Step
    <2>d. bitsliced_state' = [k \in InputSlot |-> RoundFn(bitsliced_state[k], rnd + 1)]
      BY <1>A DEF Step
    <2>e. base_states \in [InputSlot -> StateValue]       OBVIOUS
    <2>f. bitsliced_state \in [InputSlot -> StateValue]   OBVIOUS
    <2>g. rnd + 1 \in Nat                                 BY <2>a, BitsAss DEF Rounds
    <2>h. \A k \in InputSlot : base_states[k] \in StateValue
      BY <2>e
    <2>i. \A k \in InputSlot : bitsliced_state[k] \in StateValue
      BY <2>f
    <2>j. \A k \in InputSlot : RoundFn(base_states[k], rnd + 1) \in StateValue
      BY <2>h, <2>g, RoundFnType
    <2>k. \A k \in InputSlot : RoundFn(bitsliced_state[k], rnd + 1) \in StateValue
      BY <2>i, <2>g, RoundFnType
    <2>l. base_states' \in [InputSlot -> StateValue]
      BY <2>c, <2>j
    <2>m. bitsliced_state' \in [InputSlot -> StateValue]
      BY <2>d, <2>k
    <2>1. TypeInvariant'
      BY <2>a, <2>b, <2>l, <2>m, BitsAss DEF Rounds
    <2>2. RefinementHolds'
      <3> SUFFICES ASSUME NEW k \in InputSlot
                   PROVE  base_states'[k] = bitsliced_state'[k]
        OBVIOUS
      <3>1. base_states'[k] = RoundFn(base_states[k], rnd + 1)
        BY <2>c
      <3>2. bitsliced_state'[k] = RoundFn(bitsliced_state[k], rnd + 1)
        BY <2>d
      <3>3. base_states[k] = bitsliced_state[k]
        OBVIOUS
      <3> QED  BY <3>1, <3>2, <3>3
    <2> QED  BY <2>1, <2>2
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
