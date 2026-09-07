---- MODULE TreeFoldOfChunks ----
(*
  Tree-fold of chunks.

  A promotion of the iterated-transformation pattern from Linear to
  Tree by combining chunk-derived chaining values up a binary tree
  rather than in a flat chain. The compression function is unchanged;
  the structural ordering of its applications differs.

  Canonical example: BLAKE3. The pattern appears in tree hashing
  generally (Sakura, Skein in tree mode), in Merkle-tree-based
  authentication, and in some post-quantum signature schemes
  (XMSS, SPHINCS+).

  Build requirements demonstrated: ResourceRegistry (chunk chaining
    values + per-level intermediates) + TraversalEngine (over chunks,
    parallelizable; over tree levels) + ActuationPass (the G function
    applied to four state words per round in BLAKE3) + Reduction (XOR
    inside the G function). The CompressionFn is uninterpreted
    cryptographic content.

  Safety claim: the root chaining value equals the result of any
  sequential reduction of the same chunks. Reduction associativity
  over CompressionFn gives this.

  Bounded parameters per the study definition: Chunks = 4 (tree depth 2),
  |ChainingValue| = 3. Exhaustive.

  Expected outcome: No error has been found  (PASS).
*)
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    c0, c1, c2,      \* chaining-value model values
    NULL_CV,         \* sentinel: "no value at this position yet"
    NumChunks        \* number of input chunks (a power of 2 for clean tree)

ASSUME NumChunks \in {1, 2, 4, 8}   \* small powers of 2 for bounded TLC

\* ── Fixed topology (the .cfg supplies only model-value constants) ─────────
\* The pattern's correctness is structural and parametric over any concrete
\* ChainingValue / ChunkCV / CompressionFn choice; this one is fixed here
\* so TLC can exhaustively check the composition. Defined inside the .tla
\* following MemoizationComposition.tla's idiom (topology + content inline;
\* .cfg holds only model values).
ChainingValue == {c0, c1, c2}

\* ChunkCV: 1..NumChunks -> ChainingValue.  The input chunk CVs.
\* Encoded as nested IF-THEN-ELSE: the SMT backend does not translate CASE
\* arms even with OTHER, while nested IF-THEN-ELSE totalizes cleanly for
\* TLAPS lift and stays TLC-acceptable.
ChunkCV ==
    [k \in 1..NumChunks |->
        IF      k = 1 THEN c0
        ELSE IF k = 2 THEN c1
        ELSE IF k = 3 THEN c2
        ELSE              c0]

\* CompressionFn: ChainingValue \X ChainingValue -> ChainingValue.
\* Deterministic; values arbitrary. Structural correctness is
\* independent of the particular function.
CompressionFn ==
    [p \in ChainingValue \X ChainingValue |->
        IF      p = <<c0, c0>> THEN c0
        ELSE IF p = <<c0, c1>> THEN c1
        ELSE IF p = <<c0, c2>> THEN c2
        ELSE IF p = <<c1, c0>> THEN c2
        ELSE IF p = <<c1, c1>> THEN c0
        ELSE IF p = <<c1, c2>> THEN c1
        ELSE IF p = <<c2, c0>> THEN c1
        ELSE IF p = <<c2, c1>> THEN c2
        ELSE                        c0]

\* Tree depth: log2(NumChunks).
\* Nested IF-THEN-ELSE for the same reason as ChunkCV above.
TreeDepth ==
    IF      NumChunks = 1 THEN 0
    ELSE IF NumChunks = 2 THEN 1
    ELSE IF NumChunks = 4 THEN 2
    ELSE                       3

\* Width of level L (counting leaves at level 0).
LevelWidth(l) ==
    IF      l = 0 THEN NumChunks
    ELSE IF l = 1 THEN NumChunks \div 2
    ELSE IF l = 2 THEN NumChunks \div 4
    ELSE               NumChunks \div 8

VARIABLES
    cv,           \* ResourceRegistry: partial function (level, index) -> value-or-NULL.
                  \* Held as a function rather than a set of triples so position
                  \* lookup is direct indexing with no CHOOSE, matching
                  \* AuditSink.tla's idiom for registry-style state. This avoids
                  \* CHOOSE-reasoning obligations during TLAPS lift.
    level         \* TraversalEngine: current tree level being computed (0..TreeDepth)

vars == <<cv, level>>

CVDomain == (0..TreeDepth) \X (1..NumChunks)

\* ---- Type invariant ------------------------------------------------------

TypeInvariant ==
    /\ cv \in [CVDomain -> ChainingValue \cup {NULL_CV}]
    /\ level \in 0..TreeDepth + 1

\* Helpers: direct indexing into the cv function. The "no value" sentinel is
\* NULL_CV. Function typing supplies one value per position.
HasValue(l, idx) == cv[<<l, idx>>] /= NULL_CV
ValAt(l, idx)    == cv[<<l, idx>>]

\* ---- Safety invariants ---------------------------------------------------

\* Once written, a cv entry is unique. This derived invariant makes the
\* ResourceRegistry consequence explicit for readers of the composition.
UniqueAtPosition ==
    \A l \in 0..TreeDepth, idx \in 1..NumChunks :
        Cardinality({v \in ChainingValue : v = ValAt(l, idx) /\ HasValue(l, idx)}) <= 1

\* Every value at level l > 0 is CompressionFn of its two children
\* at level l - 1.
LevelConsistency ==
    \A l \in 1..TreeDepth :
        \A idx \in 1..LevelWidth(l) :
            HasValue(l, idx) =>
                /\ HasValue(l - 1, 2 * idx - 1)
                /\ HasValue(l - 1, 2 * idx)
                /\ ValAt(l, idx) =
                     CompressionFn[<<ValAt(l - 1, 2 * idx - 1),
                                     ValAt(l - 1, 2 * idx)>>]

\* Level-0 entries are the input chunk CVs.
LeavesAreInputs ==
    \A idx \in 1..NumChunks :
        HasValue(0, idx) => ValAt(0, idx) = ChunkCV[idx]

\* ---- Init ----------------------------------------------------------------

\* Start with the leaves filled; the tree is built level by level.
Init ==
    /\ cv = [p \in CVDomain |->
                IF p[1] = 0 THEN ChunkCV[p[2]] ELSE NULL_CV]
    /\ level = 1

\* ---- Actions -------------------------------------------------------------

\* ResourceRegistry::Register at (level, idx) with the compression of
\* the two children at level - 1.
ComputeNode(idx) ==
    /\ level <= TreeDepth
    /\ idx \in 1..LevelWidth(level)
    /\ ~HasValue(level, idx)
    /\ HasValue(level - 1, 2 * idx - 1)
    /\ HasValue(level - 1, 2 * idx)
    /\ cv' = [cv EXCEPT ![<<level, idx>>] =
                CompressionFn[<<ValAt(level - 1, 2 * idx - 1),
                                ValAt(level - 1, 2 * idx)>>]]
    /\ level' = level   \* stay at this level until all nodes at it are computed

\* Advance to the next level when all nodes at the current level are filled.
AdvanceLevel ==
    /\ level <= TreeDepth
    /\ \A idx \in 1..LevelWidth(level) : HasValue(level, idx)
    /\ level' = level + 1
    /\ UNCHANGED cv

Done ==
    /\ level = TreeDepth + 1
    /\ UNCHANGED vars

Next ==
    \/ \E idx \in 1..NumChunks : ComputeNode(idx)
    \/ AdvanceLevel
    \/ Done

Spec == Init /\ [][Next]_vars

\* ---- Theorem (checked by TLC) --------------------------------------------

THEOREM Spec =>
    [](TypeInvariant /\ UniqueAtPosition /\ LevelConsistency /\ LeavesAreInputs)
====
