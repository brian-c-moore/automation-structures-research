---- MODULE PropagationPassNotRequired_Proof ----
(***************************************************************************
  TLAPS proof of safety for PropagationPassNotRequired.

  Discharges the THEOREM declared in PropagationPassNotRequired.tla:
      Spec => [](TypeInvariant /\ TerminationFromCounter)

  Inductive strengthening: none. The two cfg invariants are jointly
  inductive: TerminationFromCounter is established at the Terminate
  action (its guard is `round = TargetRounds`) and preserved trivially
  thereafter (no action toggles `terminated` back).

  This proof module artifact per the TLA+ study contract.
  Mirror of EncryptThenAuthenticate_Proof's multi-action case-split
  pattern.
 ***************************************************************************)
EXTENDS PropagationPassNotRequired, Naturals, Sequences, FiniteSets, TLAPS

ASSUME TargetRoundsAss      == TargetRounds \in Nat /\ TargetRounds >= 1

\* Helper: RoundFn closure.
LEMMA RoundFnType ==
    \A s \in StateValue : RoundFn(s) \in StateValue
  BY DEF RoundFn, StateValue

\* Helper: 0 is in StateValue.
LEMMA ZeroInStateValue == 0 \in StateValue
  BY DEF StateValue

\* Inductive invariant.
Inv == TypeInvariant /\ TerminationFromCounter

LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv
    OBVIOUS
  <1>1. TypeInvariant
    <2>a. state = 0 /\ round = 0 /\ terminated = FALSE   BY DEF Init
    <2>b. 0 \in StateValue                                BY ZeroInStateValue
    <2>c. 0 \in 0..TargetRounds                           BY TargetRoundsAss
    <2>d. FALSE \in BOOLEAN                               OBVIOUS
    <2> QED  BY <2>a, <2>b, <2>c, <2>d DEF TypeInvariant
  <1>2. TerminationFromCounter
    BY DEF Init, TerminationFromCounter
  <1> QED  BY <1>1, <1>2 DEF Inv

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <1> USE DEF Inv, TypeInvariant, TerminationFromCounter
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF vars
  <1>A. CASE PropagationStep
    <2>a. ~terminated                                     BY <1>A DEF PropagationStep
    <2>b. round < TargetRounds                            BY <1>A DEF PropagationStep
    <2>c. state' = RoundFn(state)                         BY <1>A DEF PropagationStep
    <2>d. round' = round + 1                              BY <1>A DEF PropagationStep
    <2>e. UNCHANGED terminated                            BY <1>A DEF PropagationStep
    <2>f. state \in StateValue                            OBVIOUS
    <2>g. state' \in StateValue                           BY <2>c, <2>f, RoundFnType
    <2>1. TypeInvariant'
      BY <2>b, <2>d, <2>e, <2>g, TargetRoundsAss
    <2>2. TerminationFromCounter'
      BY <2>a, <2>e
    <2> QED  BY <2>1, <2>2
  <1>B. CASE Terminate
    <2>a. ~terminated                                     BY <1>B DEF Terminate
    <2>b. round = TargetRounds                            BY <1>B DEF Terminate
    <2>c. terminated' = TRUE                              BY <1>B DEF Terminate
    <2>d. UNCHANGED <<state, round>>                      BY <1>B DEF Terminate
    <2>1. TypeInvariant'
      BY <2>c, <2>d, TargetRoundsAss
    <2>2. TerminationFromCounter'
      BY <2>b, <2>c, <2>d
    <2> QED  BY <2>1, <2>2
  <1>C. CASE Done
    BY <1>C DEF Done, vars
  <1>D. CASE Next
    BY <1>D, <1>A, <1>B, <1>C DEF Next
  <1> QED  BY <1>0, <1>D

THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv                       BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'        BY NextInv
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

THEOREM TypeInvariantSafety == Spec => []TypeInvariant
  BY Safety, PTL DEF Inv

THEOREM TerminationFromCounterSafety == Spec => []TerminationFromCounter
  BY Safety, PTL DEF Inv

====
