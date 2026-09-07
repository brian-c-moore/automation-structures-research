---- MODULE TreeFoldOfChunks_Proof ----
(***************************************************************************
  TLAPS proof of safety for the TreeFoldOfChunks composition (the composition taxonomy; supplementary-research/studies/domain-corpora/cryptography/tla/compositions/).

  Discharges the THEOREM declared in TreeFoldOfChunks.tla:
      Spec => [](TypeInvariant /\ UniqueAtPosition
                                /\ LevelConsistency /\ LeavesAreInputs)

  Inductive strengthening: the four cfg invariants are jointly inductive
  without further strengthening. `cv` is reformulated as a partial function
  (positions -> ChainingValue \cup {NULL_CV}); ComputeNode mutates exactly
  one position via EXCEPT, so all four invariants are preserved by direct
  function-update reasoning (no CHOOSE).

  This proof module artifact per the TLA+ study contract
 ***************************************************************************)
EXTENDS TreeFoldOfChunks, Naturals, Sequences, FiniteSets, FiniteSetTheorems, TLAPS

\* Constants surfaced under named identifiers for use in BY clauses.
ASSUME NumChunksType == NumChunks \in {1, 2, 4, 8}
ASSUME NullCVNotInChainingValue == NULL_CV \notin ChainingValue

\* TreeDepth is a Nat in 0..3 for the bounded NumChunks.
LEMMA TreeDepthType == TreeDepth \in 0..3
  BY NumChunksType DEF TreeDepth

\* LevelWidth(l) is a Nat for l in 0..TreeDepth.
LEMMA LevelWidthType ==
    \A l \in 0..TreeDepth : LevelWidth(l) \in Nat /\ LevelWidth(l) >= 1
  BY NumChunksType, TreeDepthType DEF LevelWidth, TreeDepth

\* Children of a level-l node live at level l-1 with indices 2*idx-1 and 2*idx;
\* both must fit in 1..NumChunks. This is the doubling property: at any level
\* l >= 1, the level holds NumChunks/2^l nodes, so 2 * LevelWidth(l) = NumChunks/
\* 2^(l-1) <= NumChunks for l >= 1.
LEMMA LevelWidthDoublingBound ==
    \A l \in 1..TreeDepth : 2 * LevelWidth(l) <= NumChunks
  <1> SUFFICES ASSUME NEW l \in 1..TreeDepth PROVE 2 * LevelWidth(l) <= NumChunks
    OBVIOUS
  <1>1. CASE NumChunks = 2
    BY <1>1 DEF TreeDepth, LevelWidth
  <1>2. CASE NumChunks = 4
    BY <1>2 DEF TreeDepth, LevelWidth
  <1>3. CASE NumChunks = 8
    BY <1>3 DEF TreeDepth, LevelWidth
  <1>4. CASE NumChunks = 1
    \* TreeDepth = 0, so 1..TreeDepth is empty; assumption discharges vacuously.
    BY <1>4 DEF TreeDepth
  <1> QED  BY <1>1, <1>2, <1>3, <1>4, NumChunksType

\* ChunkCV(k) lies in ChainingValue for any k in domain.
LEMMA ChunkCVType ==
    \A k \in 1..NumChunks : ChunkCV[k] \in ChainingValue
  BY NumChunksType DEF ChunkCV, ChainingValue

\* CompressionFn maps any (ChainingValue, ChainingValue) pair into ChainingValue.
LEMMA CompressionFnType ==
    \A a \in ChainingValue, b \in ChainingValue :
        CompressionFn[<<a, b>>] \in ChainingValue
  BY DEF CompressionFn, ChainingValue

\* Strengthening: level is always at least 1. The cfg's TypeInvariant only
\* says `level \in 0..TreeDepth + 1`; the tighter `level >= 1` is what makes
\* level-1 indexing into the cv function well-defined inside ComputeNode's
\* pre-conditions. The strengthening is inductive: Init sets level = 1;
\* AdvanceLevel monotonically increments; ComputeNode is UNCHANGED level.
LevelLowerBound == level >= 1

\* Inductive invariant: the conjunction of the four cfg invariants plus the
\* level-lower-bound strengthening.
Inv == TypeInvariant /\ LevelLowerBound /\ UniqueAtPosition
                     /\ LevelConsistency /\ LeavesAreInputs

(*-------------------------------------------------------------------------*)
(* Lemma: Init establishes the inductive invariant.                        *)
(*-------------------------------------------------------------------------*)
LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv
    OBVIOUS
  <1>1. TypeInvariant
    <2>1. cv \in [CVDomain -> ChainingValue \cup {NULL_CV}]
      <3> SUFFICES ASSUME NEW p \in CVDomain
                   PROVE  (IF p[1] = 0 THEN ChunkCV[p[2]] ELSE NULL_CV)
                            \in ChainingValue \cup {NULL_CV}
        BY DEF Init
      <3>1. p[1] \in 0..TreeDepth /\ p[2] \in 1..NumChunks
        BY DEF CVDomain
      <3>2. CASE p[1] = 0
        BY <3>1, <3>2, ChunkCVType
      <3>3. CASE p[1] /= 0
        BY <3>3
      <3> QED  BY <3>2, <3>3
    <2>2. level \in 0..TreeDepth + 1
      BY TreeDepthType DEF Init
    <2> QED  BY <2>1, <2>2 DEF TypeInvariant
  <1>5. LevelLowerBound
    BY DEF Init, LevelLowerBound
  <1>2. UniqueAtPosition
    \* {v \in ChainingValue : v = ValAt(l, idx) /\ HasValue(l, idx)} is either
    \* empty (if not HasValue) or a singleton (the one value). Cardinality <= 1.
    <2> SUFFICES ASSUME NEW l \in 0..TreeDepth, NEW idx \in 1..NumChunks
                 PROVE  Cardinality({v \in ChainingValue : v = ValAt(l, idx)
                                                          /\ HasValue(l, idx)}) <= 1
      BY DEF UniqueAtPosition
    <2>1. CASE HasValue(l, idx)
      <3>1. {v \in ChainingValue : v = ValAt(l, idx) /\ HasValue(l, idx)}
              \subseteq {ValAt(l, idx)}
        BY <2>1
      <3>2. IsFiniteSet({ValAt(l, idx)})
        BY FS_Singleton
      <3>3. Cardinality({ValAt(l, idx)}) = 1
        BY FS_Singleton
      <3> QED  BY <3>1, <3>2, <3>3, FS_Subset
    <2>2. CASE ~ HasValue(l, idx)
      <3>1. {v \in ChainingValue : v = ValAt(l, idx) /\ HasValue(l, idx)} = {}
        BY <2>2
      <3> QED  BY <3>1, FS_EmptySet
    <2> QED  BY <2>1, <2>2
  <1>3. LevelConsistency
    \* No level-l >= 1 entries exist yet; the universal is vacuous.
    <2> SUFFICES ASSUME NEW l \in 1..TreeDepth, NEW idx \in 1..LevelWidth(l),
                         HasValue(l, idx)
                 PROVE  FALSE
      BY DEF LevelConsistency
    <2>1. <<l, idx>> \in CVDomain
      BY LevelWidthType, NumChunksType DEF CVDomain, LevelWidth
    <2>2. cv[<<l, idx>>] = (IF l = 0 THEN ChunkCV[idx] ELSE NULL_CV)
      BY <2>1 DEF Init
    <2>3. cv[<<l, idx>>] = NULL_CV
      BY <2>2
    <2>4. ~ HasValue(l, idx)
      BY <2>3 DEF HasValue
    <2> QED  BY <2>4
  <1>4. LeavesAreInputs
    <2> SUFFICES ASSUME NEW idx \in 1..NumChunks, HasValue(0, idx)
                 PROVE  ValAt(0, idx) = ChunkCV[idx]
      BY DEF LeavesAreInputs
    <2>1. <<0, idx>> \in CVDomain
      BY TreeDepthType DEF CVDomain
    <2>2. cv[<<0, idx>>] = ChunkCV[idx]
      BY <2>1 DEF Init
    <2> QED  BY <2>2 DEF ValAt
  <1> QED  BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF Inv

(*-------------------------------------------------------------------------*)
(* Lemma: every Next step preserves the inductive invariant.               *)
(*-------------------------------------------------------------------------*)
LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <1> USE DEF Inv, TypeInvariant, LevelLowerBound, UniqueAtPosition,
              LevelConsistency, LeavesAreInputs, HasValue, ValAt, CVDomain
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF vars
  <1>1. CASE \E idx \in 1..NumChunks : ComputeNode(idx)
    <2> SUFFICES ASSUME NEW idx \in 1..NumChunks, ComputeNode(idx)
                 PROVE  Inv'
      BY <1>1
    \* Extract post-state facts from ComputeNode's definition.
    <2>a. level <= TreeDepth                                BY DEF ComputeNode
    <2>b. idx \in 1..LevelWidth(level)                      BY DEF ComputeNode
    <2>c. ~ HasValue(level, idx)                            BY DEF ComputeNode
    <2>d. HasValue(level - 1, 2 * idx - 1)                  BY DEF ComputeNode
    <2>e. HasValue(level - 1, 2 * idx)                      BY DEF ComputeNode
    <2>f. level' = level                                    BY DEF ComputeNode
    <2>g. cv' = [cv EXCEPT ![<<level, idx>>] =
                  CompressionFn[<<ValAt(level - 1, 2 * idx - 1),
                                  ValAt(level - 1, 2 * idx)>>]]
      BY DEF ComputeNode
    \* Stage 1: typing facts about the new value and positions.
    <2>k. level \in 1..TreeDepth
      BY <2>a, TreeDepthType DEF LevelLowerBound
    <2>l. idx \in 1..LevelWidth(level)                       BY <2>b
    <2>m. <<level, idx>> \in CVDomain
      BY <2>k, <2>l, LevelWidthType, NumChunksType DEF LevelWidth
    <2>n. ValAt(level - 1, 2 * idx - 1) \in ChainingValue
      <3>1. <<level - 1, 2 * idx - 1>> \in CVDomain
        BY <2>k, <2>l, LevelWidthType, LevelWidthDoublingBound, NumChunksType, TreeDepthType DEF LevelWidth
      <3>2. cv[<<level - 1, 2 * idx - 1>>] \in ChainingValue \cup {NULL_CV}
        BY <3>1
      <3>3. cv[<<level - 1, 2 * idx - 1>>] /= NULL_CV
        BY <2>d
      <3> QED  BY <3>2, <3>3
    <2>o. ValAt(level - 1, 2 * idx) \in ChainingValue
      <3>1. <<level - 1, 2 * idx>> \in CVDomain
        BY <2>k, <2>l, LevelWidthType, LevelWidthDoublingBound, NumChunksType, TreeDepthType DEF LevelWidth
      <3>2. cv[<<level - 1, 2 * idx>>] \in ChainingValue \cup {NULL_CV}
        BY <3>1
      <3>3. cv[<<level - 1, 2 * idx>>] /= NULL_CV
        BY <2>e
      <3> QED  BY <3>2, <3>3
    <2>p. CompressionFn[<<ValAt(level - 1, 2 * idx - 1), ValAt(level - 1, 2 * idx)>>]
            \in ChainingValue
      BY <2>n, <2>o, CompressionFnType
    \* Stage 2: discharge the four conjuncts of Inv'.
    <2>1. TypeInvariant'
      <3>1. cv' \in [CVDomain -> ChainingValue \cup {NULL_CV}]
        <4>1. cv \in [CVDomain -> ChainingValue \cup {NULL_CV}]
          OBVIOUS
        <4>2. CompressionFn[<<ValAt(level - 1, 2 * idx - 1), ValAt(level - 1, 2 * idx)>>]
                \in ChainingValue \cup {NULL_CV}
          BY <2>p
        <4> QED  BY <2>g, <2>m, <4>1, <4>2
      <3>2. level' \in 0..TreeDepth + 1
        BY <2>f
      <3> QED  BY <3>1, <3>2
    <2>1b. LevelLowerBound'
      BY <2>f
    <2>2. UniqueAtPosition'
      \* Tautological for cv as a function: each position has at most one value.
      <3> SUFFICES ASSUME NEW l \in 0..TreeDepth, NEW j \in 1..NumChunks
                   PROVE  Cardinality({v \in ChainingValue :
                                           v = cv'[<<l, j>>]
                                           /\ cv'[<<l, j>>] /= NULL_CV}) <= 1
        BY DEF UniqueAtPosition
      <3>1. {v \in ChainingValue : v = cv'[<<l, j>>] /\ cv'[<<l, j>>] /= NULL_CV}
              \subseteq {cv'[<<l, j>>]}
        OBVIOUS
      <3>2. IsFiniteSet({cv'[<<l, j>>]})
        BY FS_Singleton
      <3>3. Cardinality({cv'[<<l, j>>]}) = 1
        BY FS_Singleton
      <3> QED  BY <3>1, <3>2, <3>3, FS_Subset
    <2>3. LevelConsistency'
      <3> SUFFICES ASSUME NEW l \in 1..TreeDepth, NEW j \in 1..LevelWidth(l),
                           cv'[<<l, j>>] /= NULL_CV
                   PROVE  /\ cv'[<<l - 1, 2 * j - 1>>] /= NULL_CV
                          /\ cv'[<<l - 1, 2 * j>>] /= NULL_CV
                          /\ cv'[<<l, j>>] = CompressionFn[<<cv'[<<l - 1, 2 * j - 1>>],
                                                            cv'[<<l - 1, 2 * j>>]>>]
        BY DEF LevelConsistency
      <3>1. <<l, j>> \in CVDomain
        BY LevelWidthType, LevelWidthDoublingBound, NumChunksType, TreeDepthType DEF LevelWidth
      <3>2. <<l - 1, 2 * j - 1>> \in CVDomain
        BY LevelWidthType, LevelWidthDoublingBound, NumChunksType, TreeDepthType DEF LevelWidth
      <3>3. <<l - 1, 2 * j>> \in CVDomain
        BY LevelWidthType, LevelWidthDoublingBound, NumChunksType, TreeDepthType DEF LevelWidth
      <3>A. CASE l = level /\ j = idx
        \* New entry. cv'[<<l,j>>] = NEW_VAL = CompressionFn[<<cv[children]>>]. Children unchanged.
        <4>1. cv'[<<l, j>>] = CompressionFn[<<ValAt(level - 1, 2 * idx - 1),
                                              ValAt(level - 1, 2 * idx)>>]
          BY <2>g, <3>1, <3>A
        <4>2. cv'[<<l - 1, 2 * j - 1>>] = cv[<<l - 1, 2 * j - 1>>]
          BY <2>g, <3>2, <3>A
        <4>3. cv'[<<l - 1, 2 * j>>] = cv[<<l - 1, 2 * j>>]
          BY <2>g, <3>3, <3>A
        <4>4. ValAt(level - 1, 2 * idx - 1) = cv[<<level - 1, 2 * idx - 1>>]
          OBVIOUS
        <4>5. ValAt(level - 1, 2 * idx) = cv[<<level - 1, 2 * idx>>]
          OBVIOUS
        <4>6. cv[<<level - 1, 2 * idx - 1>>] /= NULL_CV
          BY <2>d
        <4>7. cv[<<level - 1, 2 * idx>>] /= NULL_CV
          BY <2>e
        <4>8. cv'[<<l - 1, 2 * j - 1>>] /= NULL_CV
          BY <3>A, <4>2, <4>6
        <4>9. cv'[<<l - 1, 2 * j>>] /= NULL_CV
          BY <3>A, <4>3, <4>7
        <4>10. cv'[<<l, j>>] = CompressionFn[<<cv'[<<l - 1, 2 * j - 1>>],
                                                cv'[<<l - 1, 2 * j>>]>>]
          BY <3>A, <4>1, <4>2, <4>3, <4>4, <4>5
        <4> QED  BY <4>8, <4>9, <4>10
      <3>B. CASE ~ (l = level /\ j = idx)
        \* Existing entry. Key observation: under <3>B, the children's positions
        \* <<l-1, 2*j-1>> and <<l-1, 2*j>> CANNOT equal <<level, idx>>, because
        \* <<level, idx>> had NULL_CV in cv (by ComputeNode's precondition
        \* ~HasValue(level, idx)) while children must have non-NULL_CV values
        \* (by LevelConsistency at (l, j) in cv). So the EXCEPT in cv' leaves
        \* both children's values untouched, and the value equation inherits
        \* directly from cv's LevelConsistency at (l, j).
        <4>1. cv'[<<l, j>>] = cv[<<l, j>>]
          BY <2>g, <3>1, <3>B
        <4>2. cv[<<l, j>>] /= NULL_CV
          BY <4>1
        <4>3. cv[<<l, j>>] = CompressionFn[<<cv[<<l - 1, 2 * j - 1>>],
                                              cv[<<l - 1, 2 * j>>]>>]
          BY <4>2 DEF LevelConsistency
        <4>4. cv[<<l - 1, 2 * j - 1>>] /= NULL_CV
          BY <4>2 DEF LevelConsistency
        <4>5. cv[<<l - 1, 2 * j>>] /= NULL_CV
          BY <4>2 DEF LevelConsistency
        <4>6. <<l - 1, 2 * j - 1>> /= <<level, idx>>
          <5> SUFFICES ASSUME <<l - 1, 2 * j - 1>> = <<level, idx>> PROVE FALSE
            OBVIOUS
          <5>1. cv[<<level, idx>>] = NULL_CV
            BY <2>c, <2>m
          <5>2. cv[<<l - 1, 2 * j - 1>>] = NULL_CV
            BY <5>1
          <5> QED  BY <5>2, <4>4
        <4>7. <<l - 1, 2 * j>> /= <<level, idx>>
          <5> SUFFICES ASSUME <<l - 1, 2 * j>> = <<level, idx>> PROVE FALSE
            OBVIOUS
          <5>1. cv[<<level, idx>>] = NULL_CV
            BY <2>c, <2>m
          <5>2. cv[<<l - 1, 2 * j>>] = NULL_CV
            BY <5>1
          <5> QED  BY <5>2, <4>5
        <4>8. cv'[<<l - 1, 2 * j - 1>>] = cv[<<l - 1, 2 * j - 1>>]
          BY <2>g, <3>2, <4>6
        <4>9. cv'[<<l - 1, 2 * j>>] = cv[<<l - 1, 2 * j>>]
          BY <2>g, <3>3, <4>7
        <4>10. cv'[<<l - 1, 2 * j - 1>>] /= NULL_CV
          BY <4>4, <4>8
        <4>11. cv'[<<l - 1, 2 * j>>] /= NULL_CV
          BY <4>5, <4>9
        <4>12. cv'[<<l, j>>] = CompressionFn[<<cv'[<<l - 1, 2 * j - 1>>],
                                                cv'[<<l - 1, 2 * j>>]>>]
          BY <4>1, <4>3, <4>8, <4>9
        <4> QED  BY <4>10, <4>11, <4>12
      <3> QED  BY <3>A, <3>B
    <2>4. LeavesAreInputs'
      <3> SUFFICES ASSUME NEW j \in 1..NumChunks, cv'[<<0, j>>] /= NULL_CV
                   PROVE  cv'[<<0, j>>] = ChunkCV[j]
        BY DEF LeavesAreInputs
      \* ComputeNode adds at (level, idx) with level >= 1 (by <2>k); so it doesn't
      \* touch level 0. cv'[<<0, j>>] = cv[<<0, j>>].
      <3>1. <<0, j>> \in CVDomain
        BY TreeDepthType
      <3>2. <<0, j>> /= <<level, idx>>
        BY <2>k
      <3>3. cv'[<<0, j>>] = cv[<<0, j>>]
        BY <2>g, <3>1, <3>2
      <3>4. cv[<<0, j>>] /= NULL_CV
        BY <3>3
      <3>5. cv[<<0, j>>] = ChunkCV[j]
        BY <3>4 DEF LeavesAreInputs
      <3> QED  BY <3>3, <3>5
    <2> QED  BY <2>1, <2>1b, <2>2, <2>3, <2>4
  <1>2. CASE AdvanceLevel
    <2>a. cv' = cv                                            BY <1>2 DEF AdvanceLevel
    <2>b. level' = level + 1                                  BY <1>2 DEF AdvanceLevel
    <2>c. level <= TreeDepth                                  BY <1>2 DEF AdvanceLevel
    <2>1. TypeInvariant'
      BY <2>a, <2>b, <2>c, TreeDepthType
    <2>1b. LevelLowerBound'
      BY <2>b
    <2>2. UniqueAtPosition'
      BY <2>a
    <2>3. LevelConsistency'
      BY <2>a
    <2>4. LeavesAreInputs'
      BY <2>a
    <2> QED  BY <2>1, <2>1b, <2>2, <2>3, <2>4
  <1>3. CASE Done
    BY <1>3 DEF Done, vars
  <1>4. CASE Next
    BY <1>4, <1>1, <1>2, <1>3 DEF Next
  <1> QED  BY <1>0, <1>4

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

THEOREM UniqueAtPositionSafety == Spec => []UniqueAtPosition
  BY Safety, PTL DEF Inv

THEOREM LevelConsistencySafety == Spec => []LevelConsistency
  BY Safety, PTL DEF Inv

THEOREM LeavesAreInputsSafety == Spec => []LeavesAreInputs
  BY Safety, PTL DEF Inv

====
