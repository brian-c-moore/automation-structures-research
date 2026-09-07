---- MODULE ScalarMultiplicationOverGroup_Proof ----
(***************************************************************************
  TLAPS proof of safety for the ScalarMultiplicationOverGroup composition.

  Discharges the THEOREM declared in ScalarMultiplicationOverGroup.tla:
      Spec => [](TypeInvariant /\ HistoryStartsAtIdentity
                                /\ ChainedAccCorrect /\ HistoryConsistent)

  Inductive strengthening: the four cfg invariants are jointly inductive
  without further strengthening. Each Step preserves all four; index-based
  reasoning over the `history` sequence handles the chain claim without
  requiring a recursive function-fixpoint operator, following
  AuditSink_Proof.tla's and
  IteratedTransformationOverChainedState_Proof.tla's idiom.

  This proof module artifact per the TLA+ study contract. It follows
  IteratedTransformationOverChainedState_Proof.tla, differing in that RoundFn
  is defined in terms of GroupOp (one double plus one conditional add), so
  RoundFnType depends on GroupOpType, the helper for the underlying group
  operation, rather than unfolding directly.
 ***************************************************************************)
EXTENDS ScalarMultiplicationOverGroup, Naturals, Sequences, FiniteSets, TLAPS

\* Constants surfaced under named identifiers for use in BY clauses.
ASSUME ScalarBitsType == ScalarBits \in Nat /\ ScalarBits >= 1

\* Inductive invariant: the conjunction of the four cfg invariants.
Inv == TypeInvariant /\ HistoryStartsAtIdentity
                     /\ ChainedAccCorrect /\ HistoryConsistent

\* Helper: GroupOp applied to any pair of GroupElements lies in GroupElement.
\* This is the structural-group-closure lemma; associativity-commutativity
\* of GroupOp follow by enumeration of the 16-entry Z/4Z table but are
\* not required for the chain-correctness safety claim.
LEMMA GroupOpType ==
    \A a \in GroupElement, b \in GroupElement : GroupOp[<<a, b>>] \in GroupElement
  BY DEF GroupOp, GroupElement

\* Helper: RoundFn (one double-and-add step) applied to any (accumulator,
\* increment) pair lies in GroupElement. RoundFn calls GroupOp twice
\* (double-then-add); the closure follows from GroupOpType.
LEMMA RoundFnType ==
    \A a \in GroupElement, b \in GroupElement : RoundFn[<<a, b>>] \in GroupElement
  BY GroupOpType DEF RoundFn

\* Helper: BasePoint lies in GroupElement.
LEMMA BasePointType == BasePoint \in GroupElement
  BY DEF BasePoint, GroupElement

\* Helper: GroupIdentity lies in GroupElement.
LEMMA GroupIdentityType == GroupIdentity \in GroupElement
  BY DEF GroupIdentity, GroupElement

\* Helper: inputs[k] lies in GroupElement for every k in 1..ScalarBits.
\* inputs[k] is either BasePoint or GroupIdentity depending on Scalar[k];
\* both are in GroupElement.
LEMMA InputsType ==
    \A k \in 1..ScalarBits : inputs[k] \in GroupElement
  BY BasePointType, GroupIdentityType DEF inputs

(*-------------------------------------------------------------------------*)
(* Lemma: Init establishes the inductive invariant.                        *)
(*-------------------------------------------------------------------------*)
LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv
    OBVIOUS
  <1>1. TypeInvariant
    \* accumulator = GroupIdentity \in GroupElement; i = 0;
    \* history = <<GroupIdentity>>; Len(history) = 1 = 0 + 1 = i + 1.
    BY GroupIdentityType, ScalarBitsType DEF Init, TypeInvariant
  <1>2. HistoryStartsAtIdentity
    BY DEF Init, HistoryStartsAtIdentity
  <1>3. ChainedAccCorrect
    \* accumulator = GroupIdentity = history[1] = history[Len(history)].
    BY DEF Init, ChainedAccCorrect
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
  <1> USE DEF Inv, TypeInvariant, HistoryStartsAtIdentity,
              ChainedAccCorrect, HistoryConsistent
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF vars
  <1>1. CASE Step
    \* Extract the post-state facts from Step's definition.
    <2>a. i < ScalarBits                                  BY <1>1 DEF Step
    <2>b. accumulator' = RoundFn[<<accumulator, inputs[i + 1]>>]
                                                          BY <1>1 DEF Step
    <2>c. i' = i + 1                                      BY <1>1 DEF Step
    <2>d. history' = Append(history, accumulator')        BY <1>1 DEF Step
    \* Stage 1: typing facts about the post-state.
    <2>e. i + 1 \in 1..ScalarBits                         BY <2>a, ScalarBitsType
    <2>f. inputs[i + 1] \in GroupElement                  BY <2>e, InputsType
    <2>g. accumulator \in GroupElement                    OBVIOUS
    <2>h. accumulator' \in GroupElement                   BY <2>b, <2>f, <2>g, RoundFnType
    <2>i. history \in Seq(GroupElement) /\ Len(history) = i + 1
                                                          OBVIOUS
    <2>j. history' \in Seq(GroupElement) /\ Len(history') = i + 2
                                                          BY <2>d, <2>h, <2>i
    \* Stage 2: discharge the four conjuncts of Inv'.
    <2>1. TypeInvariant'
      BY <2>a, <2>c, <2>h, <2>j, ScalarBitsType
    <2>2. HistoryStartsAtIdentity'
      \* Append preserves history[1] (since Len(history) >= 1).
      <3>1. history[1] = GroupIdentity                    OBVIOUS
      <3>2. Len(history) >= 1                             BY <2>i, ScalarBitsType
      <3>3. history'[1] = history[1]
        BY <2>d, <2>i, <3>2
      <3> QED  BY <3>1, <3>3
    <2>3. ChainedAccCorrect'
      \* history' = Append(history, accumulator'), so
      \* history'[Len(history')] = accumulator'.
      <3>1. history'[Len(history')] = accumulator'
        BY <2>d, <2>i, <2>j
      <3> QED  BY <2>b, <3>1
    <2>4. HistoryConsistent'
      \* Index-based chain reasoning over the sequence (AuditSink_Proof /
      \* BeliefDeltaLifecycle_Proof / IteratedTransformationOverChainedState_Proof
      \* pattern). Split on:
      \*   k \in 1..i   — old index; history'[k] = history[k] (Append prefix),
      \*                   so the chain step inherits from HistoryConsistent.
      \*   k = i + 1 = i'  — new index; history'[k+1] = accumulator' =
      \*                   RoundFn[<<accumulator, inputs[i+1]>>] =
      \*                   RoundFn[<<history[i+1], inputs[i+1]>>]
      \*                   by ChainedAccCorrect.
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
        \* New index: history'[k+1] = history'[i+2] = accumulator'
        \* (Append tail).
        \* accumulator' = RoundFn[<<accumulator, inputs[i+1]>>] (Step).
        \* accumulator = history[Len(history)] = history[i+1]
        \* (ChainedAccCorrect).
        \* history'[k] = history'[i+1] = history[i+1] (Append prefix at i+1
        \* since i+1 <= Len(history)).
        \* inputs[k] = inputs[i+1].
        \* Combining: history'[k+1] = RoundFn[<<history'[k], inputs[k]>>].
        <4>1. history'[k + 1] = accumulator'
          BY <2>d, <2>i, <3>B
        <4>2. accumulator = history[Len(history)]
          OBVIOUS
        <4>3. Len(history) = i + 1
          BY <2>i
        <4>4. accumulator = history[i + 1]
          BY <4>2, <4>3
        <4>5. i + 1 \in 1..Len(history)
          BY <2>i, ScalarBitsType
        <4>6. history'[i + 1] = history[i + 1]
          BY <2>d, <2>i, <4>5
        <4>7. history'[k] = history[i + 1]
          BY <3>B, <4>6
        <4>8. accumulator' = RoundFn[<<accumulator, inputs[i + 1]>>]
          BY <2>b
        <4>9. accumulator' = RoundFn[<<history'[k], inputs[k]>>]
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

THEOREM HistoryStartsAtIdentitySafety == Spec => []HistoryStartsAtIdentity
  BY Safety, PTL DEF Inv

THEOREM ChainedAccCorrectSafety == Spec => []ChainedAccCorrect
  BY Safety, PTL DEF Inv

THEOREM HistoryConsistentSafety == Spec => []HistoryConsistent
  BY Safety, PTL DEF Inv

====
