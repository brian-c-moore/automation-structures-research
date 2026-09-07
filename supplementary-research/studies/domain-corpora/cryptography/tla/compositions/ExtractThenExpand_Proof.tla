---- MODULE ExtractThenExpand_Proof ----
(***************************************************************************
  TLAPS proof of safety for the ExtractThenExpand composition (HKDF).

  Discharges the THEOREM declared in ExtractThenExpand.tla:
      Spec => [](TypeInvariant /\ PhaseOrdering /\ ChainStartsAtAnchor
                 /\ ExpandChainConsistent /\ ExtractPhaseEmpty
                 /\ PrkDependsOnIkm)

  Inductive strengthening: none. The six cfg invariants are jointly
  inductive; the expand chain reasoning mirrors
  IteratedTransformationOverChainedState's sequence-history pattern.

  This proof module artifact per the TLA+ study contract
 ***************************************************************************)
EXTENDS ExtractThenExpand, Naturals, Sequences, FiniteSets, TLAPS

ASSUME ExpandBlocksType == ExpandBlocks \in Nat /\ ExpandBlocks >= 1

\* Helper: HashValue constants are well-typed.
LEMMA H0_TType == H0_T \in HashValue
  BY DEF H0_T, HashValue

LEMMA SaltIkmPrkType == SaltIkmPrk \in HashValue
  BY DEF SaltIkmPrk, HashValue

LEMMA InfoConstType == InfoConst \in Info
  BY DEF InfoConst, Info

\* Helper: HmacExpand returns a HashValue for any input in its domain.
LEMMA HmacExpandType ==
    \A a \in HashValue, b \in HashValue, c \in Info, k \in 1..ExpandBlocks :
        HmacExpand[<<a, b, c, k>>] \in HashValue
  BY ExpandBlocksType DEF HmacExpand, HashValue, Info

\* Inductive invariant.
Inv == TypeInvariant /\ PhaseOrdering /\ ChainStartsAtAnchor
       /\ ExpandChainConsistent /\ ExtractPhaseEmpty /\ PrkDependsOnIkm

(*-------------------------------------------------------------------------*)
(* Lemma: Init establishes the inductive invariant.                        *)
(*-------------------------------------------------------------------------*)
LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv
    OBVIOUS
  <1>1. TypeInvariant
    BY H0_TType, ExpandBlocksType DEF Init, TypeInvariant
  <1>2. PhaseOrdering
    BY DEF Init, PhaseOrdering
  <1>3. ChainStartsAtAnchor
    BY DEF Init, ChainStartsAtAnchor
  <1>4. ExpandChainConsistent
    \* phase = "extract"; antecedent is false.
    BY DEF Init, ExpandChainConsistent
  <1>5. ExtractPhaseEmpty
    BY DEF Init, ExtractPhaseEmpty
  <1>6. PrkDependsOnIkm
    BY DEF Init, PrkDependsOnIkm
  <1> QED  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Inv

(*-------------------------------------------------------------------------*)
(* Lemma: every Next step preserves the inductive invariant.               *)
(*-------------------------------------------------------------------------*)
LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <1> USE DEF Inv, TypeInvariant, PhaseOrdering, ChainStartsAtAnchor,
              ExpandChainConsistent, ExtractPhaseEmpty, PrkDependsOnIkm
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF vars
  <1>A. CASE ExtractStep
    <2>a. phase = "extract"                                BY <1>A DEF ExtractStep
    <2>b. prk' = SaltIkmPrk                                BY <1>A DEF ExtractStep
    <2>c. phase' = "expand"                                BY <1>A DEF ExtractStep
    <2>d. UNCHANGED <<t_history, expand_idx>>              BY <1>A DEF ExtractStep
    <2>e. t_history = <<H0_T>>
      \* From ExtractPhaseEmpty pre-state.
      BY <2>a
    <2>1. TypeInvariant'
      BY <2>b, <2>c, <2>d, SaltIkmPrkType, ExpandBlocksType
    <2>2. PhaseOrdering'
      <3>1. expand_idx' = 0
        \* From PhaseOrdering pre: phase = "extract" => expand_idx = 0.
        BY <2>a, <2>d
      <3> QED  BY <2>b, <2>c, <3>1
    <2>3. ChainStartsAtAnchor'
      BY <2>d, <2>e
    <2>4. ExpandChainConsistent'
      <3> SUFFICES ASSUME NEW k \in 1..expand_idx'
                   PROVE  t_history'[k + 1] =
                            HmacExpand[<<prk', t_history'[k], InfoConst, k>>]
        BY <2>c
      \* expand_idx' = expand_idx = 0 (from PhaseOrdering pre), so 1..0 = {} — vacuous.
      <3>1. expand_idx' = 0
        BY <2>a, <2>d
      <3>2. k \in 1..0  BY <3>1
      <3> QED  BY <3>2
    <2>5. ExtractPhaseEmpty'
      \* phase' = "expand"; antecedent of the implication is false.
      BY <2>c
    <2>6. PrkDependsOnIkm'
      BY <2>b, <2>c
    <2> QED  BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6
  <1>B. CASE ExpandStep
    <2>a. phase = "expand"                                 BY <1>B DEF ExpandStep
    <2>b. expand_idx < ExpandBlocks                        BY <1>B DEF ExpandStep
    <2> DEFINE
        next_t == HmacExpand[<<prk, t_history[Len(t_history)],
                                InfoConst, expand_idx + 1>>]
    <2>c. t_history' = Append(t_history, next_t)           BY <1>B DEF ExpandStep
    <2>d. expand_idx' = expand_idx + 1                     BY <1>B DEF ExpandStep
    <2>e. UNCHANGED <<phase, prk>>                         BY <1>B DEF ExpandStep
    \* Typing.
    <2>f. prk = SaltIkmPrk                                 BY <2>a
    <2>g. prk \in HashValue                                BY <2>f, SaltIkmPrkType
    <2>h. Len(t_history) = expand_idx + 1                  OBVIOUS
    <2>i. t_history \in Seq(HashValue)                     OBVIOUS
    <2>j. t_history[Len(t_history)] \in HashValue
      BY <2>h, <2>i, ExpandBlocksType
    <2>k. expand_idx + 1 \in 1..ExpandBlocks               BY <2>b, ExpandBlocksType
    <2>l. next_t \in HashValue
      BY <2>g, <2>j, InfoConstType, <2>k, HmacExpandType
    <2>m. t_history' \in Seq(HashValue) /\ Len(t_history') = expand_idx + 2
      BY <2>c, <2>h, <2>i, <2>l
    <2>1. TypeInvariant'
      BY <2>b, <2>d, <2>e, <2>m, ExpandBlocksType
    <2>2. PhaseOrdering'
      <3>1. phase' = "expand"                              BY <2>a, <2>e
      <3>2. prk' = SaltIkmPrk                              BY <2>e, <2>f
      <3> QED  BY <3>1, <3>2
    <2>3. ChainStartsAtAnchor'
      \* Append preserves t_history[1].
      <3>1. t_history[1] = H0_T                            OBVIOUS
      <3>2. Len(t_history) >= 1                            BY <2>h, ExpandBlocksType
      <3>3. t_history'[1] = t_history[1]
        BY <2>c, <2>h, <3>2
      <3> QED  BY <3>1, <3>3
    <2>4. ExpandChainConsistent'
      <3> SUFFICES ASSUME NEW k \in 1..expand_idx'
                   PROVE  t_history'[k + 1] =
                            HmacExpand[<<prk', t_history'[k], InfoConst, k>>]
        BY <2>a, <2>e
      <3>1. prk' = prk                                     BY <2>e
      <3>A. CASE k \in 1..expand_idx
        \* Old index: Append preserves prefix; chain inherits from pre-state.
        <4>1. k + 1 \in 1..Len(t_history)                  BY <2>h, <3>A
        <4>2. k \in 1..Len(t_history)                      BY <2>h, <3>A
        <4>3. t_history'[k + 1] = t_history[k + 1]
          BY <2>c, <2>h, <4>1
        <4>4. t_history'[k] = t_history[k]
          BY <2>c, <2>h, <4>2
        <4>5. t_history[k + 1] = HmacExpand[<<prk, t_history[k], InfoConst, k>>]
          BY <3>A, <2>a
        <4> QED  BY <3>1, <4>3, <4>4, <4>5
      <3>B. CASE k = expand_idx + 1
        \* New index: Append's tail = next_t.
        <4>1. t_history'[k + 1] = next_t
          BY <2>c, <2>h, <3>B
        <4>2. t_history'[k] = t_history[expand_idx + 1]
          BY <2>c, <2>h, <3>B
        <4>3. t_history[expand_idx + 1] = t_history[Len(t_history)]
          BY <2>h
        <4>4. t_history'[k] = t_history[Len(t_history)]
          BY <4>2, <4>3
        <4>5. next_t = HmacExpand[<<prk, t_history[Len(t_history)],
                                     InfoConst, expand_idx + 1>>]
          OBVIOUS
        <4>6. k = expand_idx + 1                            BY <3>B
        <4> QED  BY <3>1, <4>1, <4>4, <4>5, <4>6
      <3> QED  BY <2>d, <3>A, <3>B
    <2>5. ExtractPhaseEmpty'
      \* phase' = "expand", antecedent false.
      BY <2>a, <2>e
    <2>6. PrkDependsOnIkm'
      BY <2>a, <2>e, <2>f
    <2> QED  BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6
  <1>C. CASE FinishExpand
    <2>a. phase = "expand"                                 BY <1>C DEF FinishExpand
    <2>b. expand_idx = ExpandBlocks                        BY <1>C DEF FinishExpand
    <2>c. phase' = "done"                                  BY <1>C DEF FinishExpand
    <2>d. UNCHANGED <<prk, t_history, expand_idx>>         BY <1>C DEF FinishExpand
    <2>1. TypeInvariant'
      BY <2>c, <2>d, ExpandBlocksType
    <2>2. PhaseOrdering'
      BY <2>a, <2>b, <2>c, <2>d
    <2>3. ChainStartsAtAnchor'
      BY <2>d
    <2>4. ExpandChainConsistent'
      BY <2>a, <2>c, <2>d
    <2>5. ExtractPhaseEmpty'
      BY <2>c
    <2>6. PrkDependsOnIkm'
      BY <2>a, <2>c, <2>d
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

THEOREM ChainStartsAtAnchorSafety == Spec => []ChainStartsAtAnchor
  BY Safety, PTL DEF Inv

THEOREM ExpandChainConsistentSafety == Spec => []ExpandChainConsistent
  BY Safety, PTL DEF Inv

THEOREM ExtractPhaseEmptySafety == Spec => []ExtractPhaseEmpty
  BY Safety, PTL DEF Inv

THEOREM PrkDependsOnIkmSafety == Spec => []PrkDependsOnIkm
  BY Safety, PTL DEF Inv

====
