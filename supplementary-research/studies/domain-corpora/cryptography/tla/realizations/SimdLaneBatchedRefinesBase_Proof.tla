---- MODULE SimdLaneBatchedRefinesBase_Proof ----
(***************************************************************************
  TLAPS proof of safety for SimdLaneBatchedRefinesBase.

  Discharges the THEOREM declared in SimdLaneBatchedRefinesBase.tla:
      Spec => [](TypeInvariant /\ RefinementHolds)

  Inductive strengthening: none. Per-lane RoundFn applied at lockstep
  preserves the per-lane equality between base and SIMD.

  This proof module artifact per the TLA+ study contract
  Mirror of BitslicedRefinesBase_Proof.tla.
 ***************************************************************************)
EXTENDS SimdLaneBatchedRefinesBase, Naturals, Sequences, FiniteSets, TLAPS

ASSUME NAss      == N \in Nat /\ N >= 1 /\ N <= 4
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
    BY NAss, RoundsAss, BitsAss, NConcrete, MConcrete
       DEF Init, TypeInvariant, LaneIdx, StateValue, M, Init0
  <1>2. RefinementHolds
    BY DEF Init, RefinementHolds, LaneIdx
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
    <2>c. base_states' = [k \in LaneIdx |-> RoundFn(base_states[k], rnd + 1)]
      BY <1>A DEF Step
    <2>d. simd_state' = [k \in LaneIdx |-> RoundFn(simd_state[k], rnd + 1)]
      BY <1>A DEF Step
    <2>e. base_states \in [LaneIdx -> StateValue]         OBVIOUS
    <2>f. simd_state \in [LaneIdx -> StateValue]          OBVIOUS
    <2>g. rnd + 1 \in Nat                                 BY <2>a, RoundsAss
    <2>h. \A k \in LaneIdx : base_states[k] \in StateValue   BY <2>e
    <2>i. \A k \in LaneIdx : simd_state[k] \in StateValue    BY <2>f
    <2>j. \A k \in LaneIdx : RoundFn(base_states[k], rnd + 1) \in StateValue
      BY <2>h, <2>g, RoundFnType
    <2>k. \A k \in LaneIdx : RoundFn(simd_state[k], rnd + 1) \in StateValue
      BY <2>i, <2>g, RoundFnType
    <2>l. base_states' \in [LaneIdx -> StateValue]        BY <2>c, <2>j
    <2>m. simd_state' \in [LaneIdx -> StateValue]         BY <2>d, <2>k
    <2>1. TypeInvariant'
      BY <2>a, <2>b, <2>l, <2>m, RoundsAss
    <2>2. RefinementHolds'
      <3> SUFFICES ASSUME NEW k \in LaneIdx
                   PROVE  base_states'[k] = simd_state'[k]
        OBVIOUS
      <3>1. base_states'[k] = RoundFn(base_states[k], rnd + 1)
        BY <2>c
      <3>2. simd_state'[k] = RoundFn(simd_state[k], rnd + 1)
        BY <2>d
      <3>3. base_states[k] = simd_state[k]
        OBVIOUS
      <3> QED  BY <3>1, <3>2, <3>3
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
