---- MODULE TwoLayerWrap_Proof ----
(***************************************************************************
  TLAPS proof of safety for the TwoLayerWrap composition (the composition taxonomy, HMAC pattern; supplementary-research/studies/domain-corpora/cryptography/tla/compositions/).

  Discharges the THEOREM declared in TwoLayerWrap.tla:
      Spec => [](TypeInvariant /\ PhaseOrdering /\ HistoriesStartAtH0
                 /\ InnerChainConsistent /\ OuterChainConsistent
                 /\ InnerResultSnapshot /\ ChainedStateCorrect)

  Inductive strengthening: the seven cfg invariants are jointly inductive
  without further strengthening. The two-phase composition's sequential
  structure makes per-action preservation straightforward — each phase's
  chain reasoning mirrors IteratedTransformationOverChainedState's
  pattern, and the phase-transition actions (FinishInner / FinishOuter)
  preserve the chain by leaving histories untouched.

  This proof module checks the written two-layer construction.
 ***************************************************************************)
EXTENDS TwoLayerWrap, Naturals, Sequences, FiniteSets, TLAPS

ASSUME KeyLenType == KeyLen \in Nat /\ KeyLen >= 1
ASSUME MsgLenType == MsgLen \in Nat /\ MsgLen >= 1

\* Helper: derived input-length operators are Nat.
LEMMA InnerInputLenType == InnerInputLen \in Nat /\ InnerInputLen >= 2
  BY KeyLenType, MsgLenType DEF InnerInputLen

LEMMA OuterInputLenType == OuterInputLen \in Nat /\ OuterInputLen >= 2
  BY KeyLenType DEF OuterInputLen

\* Helper: H0 lies in HashState.
LEMMA H0Type == H0 \in HashState
  BY DEF H0, HashState

\* Helper: InnerInputAt(k) lies in Block for any k in 1..InnerInputLen.
LEMMA InnerInputAtType ==
    \A k \in 1..InnerInputLen :
        InnerInputAt(k) \in Block
  <1> SUFFICES ASSUME NEW k \in 1..InnerInputLen
               PROVE  InnerInputAt(k) \in Block
    OBVIOUS
  <1>0. k \in Nat  BY KeyLenType, MsgLenType, InnerInputLenType DEF InnerInputLen
  <1>1. CASE k <= KeyLen
    <2>1. InnerKey[k] \in KeyByte
      BY KeyLenType, <1>1 DEF InnerKey, KeyByte
    <2>2. InnerInputAt(k) = InnerKey[k]
      BY <1>1, KeyLenType DEF InnerInputAt
    <2> QED  BY <2>1, <2>2 DEF Block
  <1>2. CASE k > KeyLen
    <2>1. k - KeyLen \in 1..MsgLen
      BY KeyLenType, MsgLenType, <1>2 DEF InnerInputLen
    <2>2. Msg[k - KeyLen] \in MsgByte
      BY <2>1, MsgLenType DEF Msg, MsgByte
    <2>3. ~(k <= KeyLen)
      BY <1>2, KeyLenType
    <2>4. InnerInputAt(k) = Msg[k - KeyLen]
      BY <2>3, KeyLenType, MsgLenType DEF InnerInputAt
    <2> QED  BY <2>2, <2>4 DEF Block
  <1> QED  BY <1>0, <1>1, <1>2, KeyLenType

\* Helper: OuterKey[k] lies in KeyByte (hence Block) for k in 1..KeyLen.
LEMMA OuterKeyType ==
    \A k \in 1..KeyLen : OuterKey[k] \in KeyByte
  BY KeyLenType DEF OuterKey, KeyByte

\* Helper: KeyByte and HashState are subsets of Block.
LEMMA SubsetsOfBlock ==
    /\ KeyByte \subseteq Block
    /\ HashState \subseteq Block
    /\ MsgByte \subseteq Block
  BY DEF Block

\* Helper: Compress maps any (HashState, Block) pair into HashState.
LEMMA CompressType ==
    \A s \in HashState, b \in Block :
        Compress[<<s, b>>] \in HashState
  BY DEF Compress, HashState, Block, KeyByte, MsgByte

\* Inductive invariant.
Inv == TypeInvariant /\ PhaseOrdering /\ HistoriesStartAtH0
       /\ InnerChainConsistent /\ OuterChainConsistent
       /\ InnerResultSnapshot /\ ChainedStateCorrect

(*-------------------------------------------------------------------------*)
(* Lemma: Init establishes the inductive invariant.                        *)
(*-------------------------------------------------------------------------*)
LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv
    OBVIOUS
  <1>1. TypeInvariant
    BY H0Type, KeyLenType, MsgLenType
       DEF Init, TypeInvariant, InnerInputLen, OuterInputLen
  <1>2. PhaseOrdering
    BY DEF Init, PhaseOrdering, InnerInputLen, OuterInputLen
  <1>3. HistoriesStartAtH0
    BY DEF Init, HistoriesStartAtH0
  <1>4. InnerChainConsistent
    \* inner_idx = 0, so 1..inner_idx = {} — vacuous.
    BY DEF Init, InnerChainConsistent
  <1>5. OuterChainConsistent
    BY DEF Init, OuterChainConsistent
  <1>6. InnerResultSnapshot
    \* phase = "inner", antecedent is false.
    BY DEF Init, InnerResultSnapshot
  <1>7. ChainedStateCorrect
    BY DEF Init, ChainedStateCorrect
  <1> QED  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7 DEF Inv

(*-------------------------------------------------------------------------*)
(* Lemma: every Next step preserves the inductive invariant.               *)
(*-------------------------------------------------------------------------*)
LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <1> USE DEF Inv, TypeInvariant, PhaseOrdering, HistoriesStartAtH0,
              InnerChainConsistent, OuterChainConsistent,
              InnerResultSnapshot, ChainedStateCorrect
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF vars
  <1>A. CASE InnerStep
    <2>a. phase = "inner"                                   BY <1>A DEF InnerStep
    <2>b. inner_idx < InnerInputLen                         BY <1>A DEF InnerStep
    <2>c. state' = Compress[<<state, InnerInputAt(inner_idx + 1)>>]
      BY <1>A DEF InnerStep
    <2>d. inner_idx' = inner_idx + 1                        BY <1>A DEF InnerStep
    <2>e. inner_history' = Append(inner_history, state')    BY <1>A DEF InnerStep
    <2>f. UNCHANGED <<phase, outer_idx, outer_history, inner_result>>
      BY <1>A DEF InnerStep
    \* Typing.
    <2>g0. inner_idx \in 0..InnerInputLen                    OBVIOUS
    <2>g1. inner_idx \in Nat                                 BY <2>g0, InnerInputLenType
    <2>g. inner_idx + 1 \in 1..InnerInputLen                BY <2>b, <2>g0, <2>g1, KeyLenType, MsgLenType, InnerInputLenType
    <2>h. InnerInputAt(inner_idx + 1) \in Block             BY <2>g, InnerInputAtType
    <2>i. state \in HashState                               OBVIOUS
    <2>j. state' \in HashState                              BY <2>c, <2>h, <2>i, CompressType
    <2>k. Len(inner_history) = inner_idx + 1                OBVIOUS
    <2>l. inner_history \in Seq(HashState)                  OBVIOUS
    <2>m. inner_history' \in Seq(HashState) /\ Len(inner_history') = inner_idx + 2
      BY <2>e, <2>j, <2>k, <2>l
    \* TypeInvariant'.
    <2>1. TypeInvariant'
      <3>1. state' \in HashState                            BY <2>j
      <3>2. phase' \in {"inner", "outer", "done"}            BY <2>a, <2>f
      <3>3. inner_idx' \in 0..InnerInputLen                  BY <2>b, <2>d, <2>g0, <2>g1, InnerInputLenType
      <3>4. outer_idx' \in 0..OuterInputLen                  BY <2>f
      <3>5. inner_history' \in Seq(HashState)                BY <2>m
      <3>6. outer_history' \in Seq(HashState)                BY <2>f
      <3>7. inner_result' \in HashState                      BY <2>f
      <3>8. Len(inner_history') = inner_idx' + 1             BY <2>d, <2>m
      <3>9. Len(outer_history') = outer_idx' + 1             BY <2>f
      <3> QED  BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9
    \* PhaseOrdering'.
    <2>2. PhaseOrdering'
      \* phase' = "inner" (unchanged); outer_idx' = 0 (unchanged); outer_history' = <<H0>>.
      BY <2>a, <2>f
    \* HistoriesStartAtH0'.
    <2>3. HistoriesStartAtH0'
      <3>1. inner_history[1] = H0                            OBVIOUS
      <3>2. Len(inner_history) >= 1                          BY <2>k, KeyLenType, MsgLenType
      <3>3. inner_history'[1] = inner_history[1]
        BY <2>e, <2>k, <3>2
      <3>4. outer_history'[1] = outer_history[1]             BY <2>f
      <3> QED  BY <3>1, <3>3, <3>4
    \* InnerChainConsistent'.
    <2>4. InnerChainConsistent'
      <3> SUFFICES ASSUME NEW k \in 1..inner_idx'
                   PROVE  inner_history'[k + 1] =
                            Compress[<<inner_history'[k], InnerInputAt(k)>>]
        OBVIOUS
      <3>A. CASE k \in 1..inner_idx
        <4>1. k + 1 \in 1..Len(inner_history)                BY <2>k, <3>A
        <4>2. k \in 1..Len(inner_history)                    BY <2>k, <3>A
        <4>3. inner_history'[k + 1] = inner_history[k + 1]
          BY <2>e, <2>k, <4>1
        <4>4. inner_history'[k] = inner_history[k]
          BY <2>e, <2>k, <4>2
        <4>5. inner_history[k + 1] = Compress[<<inner_history[k], InnerInputAt(k)>>]
          BY <3>A
        <4> QED  BY <4>3, <4>4, <4>5
      <3>B. CASE k = inner_idx + 1
        <4>1. k = inner_idx'                                  BY <2>d, <3>B
        <4>2. inner_history'[k + 1] = state'
          BY <2>e, <2>k, <3>B
        <4>3. inner_history'[k] = inner_history[inner_idx + 1]
          BY <2>e, <2>k, <3>B
        <4>4. inner_history[inner_idx + 1] = state
          \* ChainedStateCorrect pre: phase = "inner" => state = inner_history[Len(inner_history)].
          BY <2>a, <2>k
        <4>5. state' = Compress[<<state, InnerInputAt(inner_idx + 1)>>]
          BY <2>c
        <4>6. k = inner_idx + 1                              BY <3>B
        <4> QED  BY <4>2, <4>3, <4>4, <4>5, <4>6
      <3> QED  BY <2>d, <3>A, <3>B
    \* OuterChainConsistent' (outer untouched).
    <2>5. OuterChainConsistent'
      BY <2>f
    \* InnerResultSnapshot' (phase' = "inner", antecedent false).
    <2>6. InnerResultSnapshot'
      BY <2>a, <2>f
    \* ChainedStateCorrect'.
    <2>7. ChainedStateCorrect'
      <3>1. phase' = "inner"                                  BY <2>a, <2>f
      <3>2. inner_history'[Len(inner_history')] = state'
        BY <2>e, <2>j, <2>k, <2>l
      <3> QED  BY <3>1, <3>2
    <2> QED  BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7
  <1>B. CASE FinishInner
    <2>a. phase = "inner"                                   BY <1>B DEF FinishInner
    <2>b. inner_idx = InnerInputLen                         BY <1>B DEF FinishInner
    <2>c. inner_result' = state                             BY <1>B DEF FinishInner
    <2>d. state' = H0                                       BY <1>B DEF FinishInner
    <2>e. phase' = "outer"                                  BY <1>B DEF FinishInner
    <2>f. UNCHANGED <<inner_idx, outer_idx, inner_history, outer_history>>
      BY <1>B DEF FinishInner
    <2>g. state \in HashState                               OBVIOUS
    <2>1. TypeInvariant'
      BY <2>c, <2>d, <2>e, <2>f, <2>g, H0Type, KeyLenType, MsgLenType
    <2>2. PhaseOrdering'
      <3>1. inner_idx' = InnerInputLen                       BY <2>b, <2>f
      <3>2. outer_idx' = 0
        \* PhaseOrdering pre: phase = "inner" => outer_idx = 0.
        BY <2>a, <2>f
      <3>3. phase' = "outer"                                  BY <2>e
      <3> QED  BY <3>1, <3>2, <3>3
    <2>3. HistoriesStartAtH0'
      BY <2>f
    <2>4. InnerChainConsistent'
      BY <2>f
    <2>5. OuterChainConsistent'
      \* outer_history unchanged, outer_idx = 0 (from PhaseOrdering pre).
      \* For k \in 1..outer_idx' = 1..0 = {}, vacuous.
      BY <2>a, <2>f
    <2>6. InnerResultSnapshot'
      <3>1. inner_result' = inner_history'[Len(inner_history')]
        <4>1. inner_history' = inner_history                  BY <2>f
        <4>2. Len(inner_history) = InnerInputLen + 1          BY <2>b
        <4>3. inner_history[Len(inner_history)] = state
          \* ChainedStateCorrect pre: phase = "inner" => state = inner_history[Len(inner_history)]
          BY <2>a
        <4> QED  BY <2>c, <4>1, <4>2, <4>3
      <3>2. phase' = "outer"                                   BY <2>e
      <3> QED  BY <3>1, <3>2
    <2>7. ChainedStateCorrect'
      <3>1. phase' = "outer"                                   BY <2>e
      <3>2. outer_history' = outer_history                     BY <2>f
      <3>3. outer_history = <<H0>>
        \* PhaseOrdering pre: phase = "inner" => outer_history = <<H0>>.
        BY <2>a
      <3>4. state' = H0                                        BY <2>d
      <3>5. outer_history'[Len(outer_history')] = H0
        BY <3>2, <3>3
      <3> QED  BY <3>1, <3>4, <3>5
    <2> QED  BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7
  <1>C. CASE OuterStep
    <2>a. phase = "outer"                                   BY <1>C DEF OuterStep
    <2>b. outer_idx < OuterInputLen                          BY <1>C DEF OuterStep
    <2> DEFINE
        input == IF outer_idx + 1 <= KeyLen THEN OuterKey[outer_idx + 1]
                                             ELSE inner_result
    <2>c. state' = Compress[<<state, input>>]                BY <1>C DEF OuterStep
    <2>d. outer_idx' = outer_idx + 1                         BY <1>C DEF OuterStep
    <2>e. outer_history' = Append(outer_history, state')     BY <1>C DEF OuterStep
    <2>f. UNCHANGED <<phase, inner_idx, inner_history, inner_result>>
      BY <1>C DEF OuterStep
    \* Typing.
    <2>g0. outer_idx \in 0..OuterInputLen                    OBVIOUS
    <2>g1. outer_idx \in Nat                                 BY <2>g0, OuterInputLenType
    <2>g. outer_idx + 1 \in 1..OuterInputLen                 BY <2>b, <2>g0, <2>g1, KeyLenType, OuterInputLenType
    <2>h. input \in Block
      <3>1. CASE outer_idx + 1 <= KeyLen
        <4>1. OuterKey[outer_idx + 1] \in KeyByte             BY <2>g, <3>1, KeyLenType, OuterKeyType
        <4> QED  BY <3>1, <4>1, SubsetsOfBlock
      <3>2. CASE ~(outer_idx + 1 <= KeyLen)
        <4>1. inner_result \in HashState                      OBVIOUS
        <4> QED  BY <3>2, <4>1, SubsetsOfBlock
      <3> QED  BY <3>1, <3>2
    <2>i. state \in HashState                               OBVIOUS
    <2>j. state' \in HashState                              BY <2>c, <2>h, <2>i, CompressType
    <2>k. Len(outer_history) = outer_idx + 1                OBVIOUS
    <2>l. outer_history \in Seq(HashState)                  OBVIOUS
    <2>m. outer_history' \in Seq(HashState) /\ Len(outer_history') = outer_idx + 2
      BY <2>e, <2>j, <2>k, <2>l
    <2>1. TypeInvariant'
      BY <2>b, <2>d, <2>e, <2>f, <2>g0, <2>g1, <2>j, <2>m, KeyLenType, OuterInputLenType
    <2>2. PhaseOrdering'
      <3>1. inner_idx' = InnerInputLen
        \* From PhaseOrdering pre: phase = "outer" => inner_idx = InnerInputLen.
        BY <2>a, <2>f
      <3>2. phase' = "outer"                                   BY <2>a, <2>f
      <3> QED  BY <3>1, <3>2, <2>f
    <2>3. HistoriesStartAtH0'
      <3>1. outer_history[1] = H0                              OBVIOUS
      <3>2. Len(outer_history) >= 1                            BY <2>k, KeyLenType
      <3>3. outer_history'[1] = outer_history[1]
        BY <2>e, <2>k, <3>2
      <3> QED  BY <3>1, <3>3, <2>f
    <2>4. InnerChainConsistent'
      BY <2>f
    <2>5. OuterChainConsistent'
      <3> SUFFICES ASSUME NEW k \in 1..outer_idx'
                   PROVE  outer_history'[k + 1] =
                            Compress[<<outer_history'[k],
                                        IF k <= KeyLen THEN OuterKey[k]
                                        ELSE inner_result>>]
        BY <2>f
      <3>A. CASE k \in 1..outer_idx
        <4>1. k + 1 \in 1..Len(outer_history)                  BY <2>k, <3>A
        <4>2. k \in 1..Len(outer_history)                      BY <2>k, <3>A
        <4>3. outer_history'[k + 1] = outer_history[k + 1]
          BY <2>e, <2>k, <4>1
        <4>4. outer_history'[k] = outer_history[k]
          BY <2>e, <2>k, <4>2
        <4>5. outer_history[k + 1] = Compress[<<outer_history[k],
                                                IF k <= KeyLen THEN OuterKey[k]
                                                ELSE inner_result>>]
          BY <3>A
        <4> QED  BY <4>3, <4>4, <4>5
      <3>B. CASE k = outer_idx + 1
        <4>1. k = outer_idx'                                    BY <2>d, <3>B
        <4>2. outer_history'[k + 1] = state'
          BY <2>e, <2>k, <3>B
        <4>3. outer_history'[k] = outer_history[outer_idx + 1]
          BY <2>e, <2>k, <3>B
        <4>4. outer_history[outer_idx + 1] = state
          \* ChainedStateCorrect pre: phase = "outer" => state = outer_history[Len(outer_history)].
          BY <2>a, <2>k
        <4>5. state' = Compress[<<state, input>>]
          BY <2>c
        <4>6. k <= KeyLen <=> outer_idx + 1 <= KeyLen
          BY <3>B
        <4>7. (IF k <= KeyLen THEN OuterKey[k] ELSE inner_result) = input
          BY <3>B, <4>6
        <4> QED  BY <4>2, <4>3, <4>4, <4>5, <4>7
      <3> QED  BY <2>d, <3>A, <3>B
    <2>6. InnerResultSnapshot'
      \* phase' = "outer"; inner_result and inner_history unchanged.
      <3>1. inner_result' = inner_history'[Len(inner_history')]
        BY <2>a, <2>f
      <3> QED  BY <2>a, <2>f, <3>1
    <2>7. ChainedStateCorrect'
      <3>1. phase' = "outer"                                    BY <2>a, <2>f
      <3>2. outer_history'[Len(outer_history')] = state'
        BY <2>e, <2>j, <2>k, <2>l
      <3> QED  BY <3>1, <3>2
    <2> QED  BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7
  <1>D. CASE FinishOuter
    <2>a. phase = "outer"                                    BY <1>D DEF FinishOuter
    <2>b. outer_idx = OuterInputLen                          BY <1>D DEF FinishOuter
    <2>c. phase' = "done"                                    BY <1>D DEF FinishOuter
    <2>d. UNCHANGED <<state, inner_idx, outer_idx,
                       inner_history, outer_history, inner_result>>
      BY <1>D DEF FinishOuter
    <2>1. TypeInvariant'
      BY <2>c, <2>d, KeyLenType, MsgLenType
    <2>2. PhaseOrdering'
      <3>1. inner_idx' = InnerInputLen
        BY <2>a, <2>d
      <3>2. outer_idx' = OuterInputLen
        BY <2>b, <2>d
      <3> QED  BY <2>c, <3>1, <3>2, <2>d
    <2>3. HistoriesStartAtH0'
      BY <2>d
    <2>4. InnerChainConsistent'
      BY <2>d
    <2>5. OuterChainConsistent'
      BY <2>d
    <2>6. InnerResultSnapshot'
      BY <2>a, <2>c, <2>d
    <2>7. ChainedStateCorrect'
      \* phase' = "done", neither inner nor outer antecedent triggers.
      BY <2>c
    <2> QED  BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7
  <1>E. CASE Done
    BY <1>E DEF Done, vars
  <1>F. CASE Next
    BY <1>F, <1>A, <1>B, <1>C, <1>D, <1>E DEF Next
  <1> QED  BY <1>0, <1>F

(*-------------------------------------------------------------------------*)
(* Main safety theorem.                                                    *)
(*-------------------------------------------------------------------------*)
THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv                       BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'        BY NextInv
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

(*-------------------------------------------------------------------------*)
(* Per-invariant corollaries.                                              *)
(*-------------------------------------------------------------------------*)
THEOREM TypeInvariantSafety == Spec => []TypeInvariant
  BY Safety, PTL DEF Inv

THEOREM PhaseOrderingSafety == Spec => []PhaseOrdering
  BY Safety, PTL DEF Inv

THEOREM HistoriesStartAtH0Safety == Spec => []HistoriesStartAtH0
  BY Safety, PTL DEF Inv

THEOREM InnerChainConsistentSafety == Spec => []InnerChainConsistent
  BY Safety, PTL DEF Inv

THEOREM OuterChainConsistentSafety == Spec => []OuterChainConsistent
  BY Safety, PTL DEF Inv

THEOREM InnerResultSnapshotSafety == Spec => []InnerResultSnapshot
  BY Safety, PTL DEF Inv

THEOREM ChainedStateCorrectSafety == Spec => []ChainedStateCorrect
  BY Safety, PTL DEF Inv

====
