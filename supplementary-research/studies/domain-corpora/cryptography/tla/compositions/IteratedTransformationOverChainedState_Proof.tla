---- MODULE IteratedTransformationOverChainedState_Proof ----
(***************************************************************************
  TLAPS proof of safety for the IteratedTransformationOverChainedState
  composition.

  Discharges the THEOREM declared in IteratedTransformationOverChainedState.tla:
      Spec => [](TypeInvariant /\ HistoryStartsAtInit
                                /\ ChainedStateCorrect /\ HistoryConsistent)

  Inductive strengthening: the four cfg invariants are jointly inductive
  without further strengthening. Each Step preserves all four; index-based
  reasoning over the `history` sequence handles the chain claim without
  requiring a recursive function-fixpoint operator, following
  AuditSink_Proof.tla's idiom.

  This proof module artifact per the TLA+ study contract.
 ***************************************************************************)
EXTENDS IteratedTransformationOverChainedState, Naturals, Sequences, FiniteSets, TLAPS

\* Constants surfaced under named identifiers for use in BY clauses.
ASSUME ChainLengthType == ChainLength \in Nat /\ ChainLength >= 1

\* Inductive invariant: the conjunction of the four cfg invariants.
Inv == TypeInvariant /\ HistoryStartsAtInit
                     /\ ChainedStateCorrect /\ HistoryConsistent

\* Helper: RoundFn applied to any (state, input) pair lies in State.
LEMMA RoundFnType ==
    \A s \in State, x \in Input : RoundFn[<<s, x>>] \in State
  BY DEF RoundFn, State, Input

\* Helper: inputs[k] is an Input element for every k in 1..ChainLength.
LEMMA InputsType ==
    \A k \in 1..ChainLength : inputs[k] \in Input
  BY DEF inputs, Input

\* Helper: InitialState lies in State.
LEMMA InitialStateType == InitialState \in State
  BY DEF InitialState, State

(*-------------------------------------------------------------------------*)
(* Lemma: Init establishes the inductive invariant.                        *)
(*-------------------------------------------------------------------------*)
LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv
    OBVIOUS
  <1>1. TypeInvariant
    \* state = InitialState \in State; i = 0; history = <<InitialState>>;
    \* Len(history) = 1 = 0 + 1 = i + 1.
    BY InitialStateType, ChainLengthType DEF Init, TypeInvariant
  <1>2. HistoryStartsAtInit
    BY DEF Init, HistoryStartsAtInit
  <1>3. ChainedStateCorrect
    \* state = InitialState = history[1] = history[Len(history)].
    BY DEF Init, ChainedStateCorrect
  <1>4. HistoryConsistent
    \* The body of HistoryConsistent quantifies over k \in 1..i = 1..0 = {};
    \* the universal is vacuous.
    BY DEF Init, HistoryConsistent
  <1> QED  BY <1>1, <1>2, <1>3, <1>4 DEF Inv

(*-------------------------------------------------------------------------*)
(* Lemma: every Next step preserves the inductive invariant.               *)
(*-------------------------------------------------------------------------*)
LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <1> USE DEF Inv, TypeInvariant, HistoryStartsAtInit,
              ChainedStateCorrect, HistoryConsistent
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF vars
  <1>1. CASE Step
    \* Extract the post-state facts from Step's definition.
    <2>a. i < ChainLength                                 BY <1>1 DEF Step
    <2>b. state' = RoundFn[<<state, inputs[i + 1]>>]      BY <1>1 DEF Step
    <2>c. i' = i + 1                                       BY <1>1 DEF Step
    <2>d. history' = Append(history, state')               BY <1>1 DEF Step
    \* Stage 1: typing facts about the post-state.
    <2>e. i + 1 \in 1..ChainLength                         BY <2>a, ChainLengthType
    <2>f. inputs[i + 1] \in Input                          BY <2>e, InputsType
    <2>g. state \in State                                  OBVIOUS
    <2>h. state' \in State                                 BY <2>b, <2>f, <2>g, RoundFnType
    <2>i. history \in Seq(State) /\ Len(history) = i + 1   OBVIOUS
    <2>j. history' \in Seq(State) /\ Len(history') = i + 2 BY <2>d, <2>h, <2>i
    \* Stage 2: discharge the four conjuncts of Inv'.
    <2>1. TypeInvariant'
      BY <2>a, <2>c, <2>h, <2>j, ChainLengthType
    <2>2. HistoryStartsAtInit'
      \* Append preserves history[1] (since Len(history) >= 1).
      <3>1. history[1] = InitialState                      OBVIOUS
      <3>2. Len(history) >= 1                              BY <2>i, ChainLengthType
      <3>3. history'[1] = history[1]
        BY <2>d, <2>i, <3>2
      <3> QED  BY <3>1, <3>3
    <2>3. ChainedStateCorrect'
      \* history' = Append(history, state'), so history'[Len(history')] = state'.
      <3>1. history'[Len(history')] = state'
        BY <2>d, <2>i, <2>j
      <3> QED  BY <2>b, <3>1
    <2>4. HistoryConsistent'
      \* Index-based chain reasoning over the sequence (AuditSink_Proof
      \* / BeliefDeltaLifecycle_Proof pattern). Split on:
      \*   k \in 1..i   — old index; history'[k] = history[k] (Append prefix),
      \*                   so the chain step inherits from HistoryConsistent.
      \*   k = i + 1 = i'  — new index; history'[k+1] = state' = RoundFn[
      \*                   <<state, inputs[i+1]>>] = RoundFn[<<history[i+1],
      \*                   inputs[i+1]>>] by ChainedStateCorrect.
      <3> SUFFICES ASSUME NEW k \in 1..i'
                   PROVE  history'[k + 1] = RoundFn[<<history'[k], inputs[k]>>]
        OBVIOUS
      <3>A. CASE k \in 1..i
        \* Old indices: Append leaves history'[k] and history'[k+1] equal
        \* to history[k] and history[k+1] respectively, since k+1 <= i+1 =
        \* Len(history).
        <4>1. k + 1 \in 1..Len(history)
          BY <2>i, <3>A
        <4>2. k \in 1..Len(history)
          BY <2>i, <3>A
        <4>3. history'[k + 1] = history[k + 1]
          BY <2>d, <2>i, <4>1
        <4>4. history'[k] = history[k]
          BY <2>d, <2>i, <4>2
        <4>5. history[k + 1] = RoundFn[<<history[k], inputs[k]>>]
          BY <3>A
        <4> QED  BY <4>3, <4>4, <4>5
      <3>B. CASE k = i + 1
        \* New index: history'[k+1] = history'[i+2] = state' (Append tail).
        \* state' = RoundFn[<<state, inputs[i+1]>>] (Step).
        \* state = history[Len(history)] = history[i+1] (ChainedStateCorrect).
        \* history'[k] = history'[i+1] = history[i+1] (Append prefix at i+1
        \* since i+1 <= Len(history)).
        \* inputs[k] = inputs[i+1].
        \* Combining: history'[k+1] = RoundFn[<<history'[k], inputs[k]>>].
        <4>1. history'[k + 1] = state'
          BY <2>d, <2>i, <3>B
        <4>2. state = history[Len(history)]
          OBVIOUS
        <4>3. Len(history) = i + 1
          BY <2>i
        <4>4. state = history[i + 1]
          BY <4>2, <4>3
        <4>5. i + 1 \in 1..Len(history)
          BY <2>i, ChainLengthType
        <4>6. history'[i + 1] = history[i + 1]
          BY <2>d, <2>i, <4>5
        <4>7. history'[k] = history[i + 1]
          BY <3>B, <4>6
        <4>8. state' = RoundFn[<<state, inputs[i + 1]>>]
          BY <2>b
        <4>9. state' = RoundFn[<<history'[k], inputs[k]>>]
          BY <3>B, <4>4, <4>7, <4>8
        <4> QED  BY <4>1, <4>9
      <3> QED  BY <2>c, <3>A, <3>B
    <2> QED  BY <2>1, <2>2, <2>3, <2>4
  <1>2. CASE Done
    BY <1>2 DEF Done, vars
  <1>3. CASE Next
    BY <1>3, <1>1, <1>2 DEF Next
  <1> QED  BY <1>0, <1>3

(*-------------------------------------------------------------------------*)
(* Main safety theorem (parametric over CONSTANTS).                        *)
(*-------------------------------------------------------------------------*)
THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv                       BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'        BY NextInv
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

(*-------------------------------------------------------------------------*)
(* Per-invariant corollaries — discharge the cfg's four invariants.        *)
(*-------------------------------------------------------------------------*)
THEOREM TypeInvariantSafety == Spec => []TypeInvariant
  BY Safety, PTL DEF Inv

THEOREM HistoryStartsAtInitSafety == Spec => []HistoryStartsAtInit
  BY Safety, PTL DEF Inv

THEOREM ChainedStateCorrectSafety == Spec => []ChainedStateCorrect
  BY Safety, PTL DEF Inv

THEOREM HistoryConsistentSafety == Spec => []HistoryConsistent
  BY Safety, PTL DEF Inv

====
