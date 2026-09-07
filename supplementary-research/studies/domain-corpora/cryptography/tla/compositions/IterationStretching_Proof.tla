---- MODULE IterationStretching_Proof ----
(***************************************************************************
  TLAPS proof of safety for the IterationStretching composition (PBKDF2).

  Discharges the THEOREM declared in IterationStretching.tla:
      Spec => [](TypeInvariant /\ PhaseOrdering /\ UChainStartsAtBlockStart
                 /\ UChainConsistent /\ BlockAccCorrect
                 /\ OutputsLenTracksBlockIdx)

  Inductive strengthening: none. The six cfg invariants are jointly
  inductive without further strengthening.

  This proof module artifact per the TLA+ study contract
 ***************************************************************************)
EXTENDS IterationStretching, Naturals, Sequences, FiniteSets, TLAPS

ASSUME cType         == c \in Nat /\ c >= 1
ASSUME BlockCountAss == BlockCount \in Nat /\ BlockCount >= 1

\* Helper: H0 is in HashValue.
LEMMA H0Type == H0 \in HashValue
  BY DEF H0, HashValue

\* Helper: StartFn[i] is in HashValue for any i in 1..BlockCount.
LEMMA StartFnType ==
    \A i \in 1..BlockCount : StartFn[i] \in HashValue
  BY BlockCountAss DEF StartFn, HashValue

\* Helper: StepFn[v] is in HashValue for any v in HashValue.
LEMMA StepFnType ==
    \A v \in HashValue : StepFn[v] \in HashValue
  BY DEF StepFn, HashValue

\* Helper: Xor[<<a, b>>] is in HashValue for any (a, b) in HashValue \X HashValue.
LEMMA XorType ==
    \A a \in HashValue, b \in HashValue : Xor[<<a, b>>] \in HashValue
  BY DEF Xor, HashValue

\* Inductive invariant.
Inv == TypeInvariant /\ PhaseOrdering /\ UChainStartsAtBlockStart
       /\ UChainConsistent /\ BlockAccCorrect /\ OutputsLenTracksBlockIdx

(*-------------------------------------------------------------------------*)
(* Lemma: Init establishes the inductive invariant.                        *)
(*-------------------------------------------------------------------------*)
LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv
    OBVIOUS
  <1>1. TypeInvariant
    BY H0Type, cType, BlockCountAss DEF Init, TypeInvariant
  <1>2. PhaseOrdering
    BY DEF Init, PhaseOrdering, BetweenBlocks
  <1>3. UChainStartsAtBlockStart
    \* WithinBlock = u_idx > 0; Init has u_idx = 0, antecedent false.
    BY DEF Init, UChainStartsAtBlockStart, WithinBlock
  <1>4. UChainConsistent
    BY DEF Init, UChainConsistent, WithinBlock
  <1>5. BlockAccCorrect
    BY DEF Init, BlockAccCorrect, WithinBlock
  <1>6. OutputsLenTracksBlockIdx
    BY DEF Init, OutputsLenTracksBlockIdx
  <1> QED  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Inv

(*-------------------------------------------------------------------------*)
(* Lemma: every Next step preserves the inductive invariant.               *)
(*-------------------------------------------------------------------------*)
LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <1> USE DEF Inv, TypeInvariant, PhaseOrdering, UChainStartsAtBlockStart,
              UChainConsistent, BlockAccCorrect, OutputsLenTracksBlockIdx,
              BetweenBlocks, WithinBlock
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF vars
  <1>A. CASE StartBlock
    <2>a. block_idx <= BlockCount                          BY <1>A DEF StartBlock
    <2>b. u_idx = 0                                        BY <1>A DEF StartBlock
    <2> DEFINE u1 == StartFn[block_idx]
    <2>c. u_chain' = <<u1>>                                BY <1>A DEF StartBlock
    <2>d. block_acc' = u1                                  BY <1>A DEF StartBlock
    <2>e. u_idx' = 1                                       BY <1>A DEF StartBlock
    <2>f. UNCHANGED <<block_idx, outputs>>                 BY <1>A DEF StartBlock
    <2>g. block_idx \in 1..BlockCount                      BY <2>a, BlockCountAss
    <2>h. u1 \in HashValue                                 BY <2>g, StartFnType
    <2>i. u_chain' \in Seq(HashValue) /\ Len(u_chain') = 1 BY <2>c, <2>h
    <2>1. TypeInvariant'
      BY <2>a, <2>d, <2>e, <2>f, <2>h, <2>i, cType, BlockCountAss
    <2>2. PhaseOrdering'
      \* phase'-style: u_idx' = 1 > 0 means WithinBlock' = TRUE. No BetweenBlocks.
      \* block_idx' = block_idx <= BlockCount, so /= BlockCount + 1.
      BY <2>a, <2>e, <2>f, BlockCountAss
    <2>3. UChainStartsAtBlockStart'
      <3>1. u_chain'[1] = u1                               BY <2>c
      <3>2. block_idx' = block_idx                          BY <2>f
      <3> QED  BY <3>1, <3>2
    <2>4. UChainConsistent'
      \* u_idx' = 1, so 1..(u_idx' - 1) = 1..0 = {} — vacuous.
      BY <2>e
    <2>5. BlockAccCorrect'
      BY <2>d, <2>e, <2>h
    <2>6. OutputsLenTracksBlockIdx'
      BY <2>f
    <2> QED  BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6
  <1>B. CASE ContinueBlock
    <2>a. u_idx >= 1                                       BY <1>B DEF ContinueBlock
    <2>b. u_idx < c                                        BY <1>B DEF ContinueBlock
    <2> DEFINE next_u == StepFn[u_chain[u_idx]]
    <2>c. u_chain' = Append(u_chain, next_u)               BY <1>B DEF ContinueBlock
    <2>d. block_acc' = Xor[<<block_acc, next_u>>]          BY <1>B DEF ContinueBlock
    <2>e. u_idx' = u_idx + 1                               BY <1>B DEF ContinueBlock
    <2>f. UNCHANGED <<block_idx, outputs>>                 BY <1>B DEF ContinueBlock
    <2>g. u_chain \in Seq(HashValue) /\ Len(u_chain) = u_idx OBVIOUS
    <2>h. u_idx \in 1..c                                   BY <2>a, <2>b, cType
    <2>i. u_chain[u_idx] \in HashValue
      BY <2>g, <2>h
    <2>j. next_u \in HashValue                             BY <2>i, StepFnType
    <2>k. block_acc \in HashValue
      \* From BlockAccCorrect pre: WithinBlock => block_acc \in HashValue.
      \* WithinBlock holds because u_idx >= 1.
      BY <2>a
    <2>l. block_acc' \in HashValue                         BY <2>d, <2>j, <2>k, XorType
    <2>m. u_chain' \in Seq(HashValue) /\ Len(u_chain') = u_idx + 1
      BY <2>c, <2>g, <2>j
    <2>1. TypeInvariant'
      BY <2>a, <2>b, <2>e, <2>f, <2>l, <2>m, cType, BlockCountAss
    <2>2. PhaseOrdering'
      \* u_idx' = u_idx + 1 > 0 (since u_idx >= 1). Not between blocks.
      BY <2>a, <2>e, <2>f
    <2>3. UChainStartsAtBlockStart'
      \* u_chain'[1] = u_chain[1] (Append preserves prefix).
      <3>1. u_chain[1] = StartFn[block_idx]
        \* From UChainStartsAtBlockStart pre: WithinBlock => u_chain[1] = StartFn[block_idx].
        BY <2>a
      <3>2. u_chain'[1] = u_chain[1]
        BY <2>c, <2>g, <2>a
      <3>3. block_idx' = block_idx                          BY <2>f
      <3> QED  BY <2>e, <3>1, <3>2, <3>3
    <2>4. UChainConsistent'
      <3> SUFFICES ASSUME NEW k \in 1..(u_idx' - 1)
                   PROVE  u_chain'[k + 1] = StepFn[u_chain'[k]]
        BY <2>e
      <3>A. CASE k \in 1..(u_idx - 1)
        <4>1. k + 1 \in 1..u_idx                            BY <3>A
        <4>2. k \in 1..u_idx                                BY <3>A
        <4>3. u_chain'[k + 1] = u_chain[k + 1]
          BY <2>c, <2>g, <4>1
        <4>4. u_chain'[k] = u_chain[k]
          BY <2>c, <2>g, <4>2
        <4>5. u_chain[k + 1] = StepFn[u_chain[k]]
          BY <3>A, <2>a
        <4> QED  BY <4>3, <4>4, <4>5
      <3>B. CASE k = u_idx
        <4>1. u_chain'[k + 1] = next_u
          BY <2>c, <2>g, <3>B
        <4>2. u_chain'[k] = u_chain[u_idx]
          BY <2>c, <2>g, <3>B
        <4>3. next_u = StepFn[u_chain[u_idx]]               OBVIOUS
        <4> QED  BY <3>B, <4>1, <4>2, <4>3
      <3> QED  BY <2>e, <3>A, <3>B
    <2>5. BlockAccCorrect'
      BY <2>a, <2>e, <2>l
    <2>6. OutputsLenTracksBlockIdx'
      BY <2>f
    <2> QED  BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6
  <1>C. CASE FinishBlock
    <2>a. u_idx = c                                        BY <1>C DEF FinishBlock
    <2>b. outputs' = Append(outputs, block_acc)            BY <1>C DEF FinishBlock
    <2>c. block_idx' = block_idx + 1                       BY <1>C DEF FinishBlock
    <2>d. u_idx' = 0                                       BY <1>C DEF FinishBlock
    <2>e. u_chain' = <<>>                                  BY <1>C DEF FinishBlock
    <2>f. block_acc' = H0                                  BY <1>C DEF FinishBlock
    <2>g. block_acc \in HashValue
      \* From BlockAccCorrect pre (WithinBlock = u_idx = c >= 1).
      BY <2>a, cType
    <2>h. outputs \in Seq(HashValue)                       OBVIOUS
    <2>i. outputs' \in Seq(HashValue) /\ Len(outputs') = Len(outputs) + 1
      BY <2>b, <2>g, <2>h
    <2>1. TypeInvariant'
      <3>1. block_idx + 1 \in 1..BlockCount + 1
        \* block_idx is in 1..BlockCount (since FinishBlock fires after a Start;
        \* StartBlock requires block_idx <= BlockCount).
        \* But TypeInvariant pre only says block_idx \in 1..BlockCount + 1, so
        \* the argument runs through PhaseOrdering: block_idx = BlockCount + 1 =>
        \* BetweenBlocks => u_idx = 0, contradicting u_idx = c >= 1.
        <4>1. block_idx <= BlockCount
          <5> SUFFICES ASSUME block_idx > BlockCount PROVE FALSE
            BY BlockCountAss
          <5>1. block_idx = BlockCount + 1
            BY BlockCountAss
          <5>2. u_idx = 0
            \* From PhaseOrdering pre.
            BY <5>1
          <5> QED  BY <5>2, <2>a, cType
        <4> QED  BY <4>1, BlockCountAss
      <3>2. u_idx' \in 0..c                                 BY <2>d, cType
      <3>3. u_chain' \in Seq(HashValue) /\ Len(u_chain') = u_idx'
        BY <2>d, <2>e
      <3>4. block_acc' \in HashValue                        BY <2>f, H0Type
      <3>5. Len(outputs') = block_idx' - 1
        \* Len(outputs) = block_idx - 1 (from OutputsLenTracksBlockIdx pre).
        \* Len(outputs') = Len(outputs) + 1 = block_idx.
        \* block_idx' - 1 = block_idx.
        <4>1. Len(outputs) = block_idx - 1                  OBVIOUS
        <4>2. Len(outputs') = Len(outputs) + 1              BY <2>i
        <4> QED  BY <2>c, <4>1, <4>2, BlockCountAss
      <3> QED  BY <2>c, <3>1, <3>2, <3>3, <3>4, <3>5, <2>i
    <2>2. PhaseOrdering'
      \* u_idx' = 0 = BetweenBlocks'. u_chain' = <<>> ok. block_acc' = H0 ok.
      <3>1. BetweenBlocks'                                   BY <2>d
      <3>2. u_chain' = <<>>                                  BY <2>e
      <3>3. block_acc' = H0                                  BY <2>f
      <3>4. block_idx' \in 1..BlockCount + 1
        \* (from TypeInvariant' which we just proved).
        BY <2>1
      <3> QED  BY <3>1, <3>2, <3>3, <3>4
    <2>3. UChainStartsAtBlockStart'
      \* WithinBlock' = u_idx' > 0 = FALSE; antecedent false.
      BY <2>d
    <2>4. UChainConsistent'
      BY <2>d
    <2>5. BlockAccCorrect'
      BY <2>d
    <2>6. OutputsLenTracksBlockIdx'
      <3>1. Len(outputs) = block_idx - 1                    OBVIOUS
      <3>2. Len(outputs') = Len(outputs) + 1                BY <2>i
      <3> QED  BY <2>c, <3>1, <3>2, BlockCountAss
    <2> QED  BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6
  <1>D. CASE Done
    BY <1>D DEF Done, vars
  <1>E. CASE Next
    BY <1>E, <1>A, <1>B, <1>C, <1>D DEF Next
  <1> QED  BY <1>0, <1>E

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

THEOREM UChainStartsAtBlockStartSafety == Spec => []UChainStartsAtBlockStart
  BY Safety, PTL DEF Inv

THEOREM UChainConsistentSafety == Spec => []UChainConsistent
  BY Safety, PTL DEF Inv

THEOREM BlockAccCorrectSafety == Spec => []BlockAccCorrect
  BY Safety, PTL DEF Inv

THEOREM OutputsLenTracksBlockIdxSafety == Spec => []OutputsLenTracksBlockIdx
  BY Safety, PTL DEF Inv

====
