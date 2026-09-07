---- MODULE ExtractThenExpand ----
(*
  Extract-then-expand (the composition taxonomy, HKDF).

  Two-phase key-derivation composition: an "extract" step distills entropy
  from input keying material (IKM) and a salt into a pseudo-random key
  (PRK); an "expand" chain then derives a sequence of output blocks
  T_1, T_2, ..., T_n where T_{i+1} = HMAC(PRK, T_i || info || i+1).

  Canonical example: HKDF-SHA-256. The pattern is the dominant
  modern key-derivation shape (TLS 1.3, Signal, Noise framework).

  Build requirements demonstrated: ResourceRegistry (PRK + T-chain) +
    TraversalEngine (over expand iterations) + ActuationPass (per-block
    HMAC call). HMAC is uninterpreted cryptographic content; both
    HmacExtract and HmacExpand are parametric.

  Safety claims:
    PrkDependsOnIkm — after the extract phase, prk = HmacExtract(salt, ikm).
    ExpandChainConsistent — each T_{i+1} in the chain equals HmacExpand
      applied to (prk, T_i, info, i+1). Every expand block transitively
      depends on prk, hence on the extract input.
    PhaseOrdering — expand begins only after extract finishes.

  Bounded parameters per the study definition: ExtractMsg = 2 IKM bytes
  (abstracted to a single PRK output), ExpandBlocks = 3. Exhaustive.

  Expected outcome: No error has been found  (PASS).
*)
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    h0, h1, h2, h3,    \* hash / chaining value model values (PRK and T values)
    info0, info1,      \* info-byte model values (the "info" parameter)
    ExpandBlocks       \* number of expand iterations (output blocks)

ASSUME ExpandBlocks \in Nat /\ ExpandBlocks >= 1

\* ── Fixed topology (the .cfg supplies only model-value constants) ─────────
HashValue == {h0, h1, h2, h3}
Info      == {info0, info1}

H0_T  == h0   \* distinguished T_0 empty-sequence anchor
SaltIkmPrk == h1   \* the (concrete) PRK resulting from extract; abstracts
                   \* HmacExtract(salt, ikm) to a single result value.

\* HmacExpand: HashValue \X HashValue \X Info \X 1..ExpandBlocks -> HashValue.
\* Deterministic; structural correctness independent of the particular content.
HmacExpand ==
    [p \in HashValue \X HashValue \X Info \X (1..ExpandBlocks) |->
        IF      p = <<h0, h0, info0, 1>> THEN h1
        ELSE IF p = <<h0, h0, info0, 2>> THEN h2
        ELSE IF p = <<h0, h0, info0, 3>> THEN h3
        ELSE IF p = <<h0, h1, info0, 1>> THEN h2
        ELSE IF p = <<h0, h1, info0, 2>> THEN h3
        ELSE IF p = <<h0, h1, info0, 3>> THEN h0
        ELSE IF p = <<h1, h0, info0, 1>> THEN h2
        ELSE IF p = <<h1, h0, info0, 2>> THEN h3
        ELSE IF p = <<h1, h0, info0, 3>> THEN h0
        ELSE IF p = <<h1, h1, info0, 1>> THEN h0
        ELSE IF p = <<h1, h1, info0, 2>> THEN h1
        ELSE IF p = <<h1, h1, info0, 3>> THEN h2
        ELSE                                  h3]

\* InfoConst: the fixed info parameter (k-th info byte; a single byte info0
\* is used throughout the expand chain).
InfoConst == info0

VARIABLES
    phase,             \* "extract" / "expand" / "done"
    prk,               \* the extract phase's output PRK (HashValue)
    t_history,         \* chain of T values (Seq(HashValue)); T_0 = H0_T,
                       \* T_i is at position i+1.
    expand_idx         \* progress in expand phase (0..ExpandBlocks)

vars == <<phase, prk, t_history, expand_idx>>

\* ---- Type invariant ------------------------------------------------------

TypeInvariant ==
    /\ phase \in {"extract", "expand", "done"}
    /\ prk \in HashValue
    /\ t_history \in Seq(HashValue)
    /\ expand_idx \in 0..ExpandBlocks
    /\ Len(t_history) = expand_idx + 1

\* ---- Safety invariants ---------------------------------------------------

\* Phases progress in order: extract before expand before done.
PhaseOrdering ==
    /\ phase = "extract" => expand_idx = 0
    /\ (phase = "expand" \/ phase = "done") => prk = SaltIkmPrk
    /\ phase = "done" => expand_idx = ExpandBlocks

\* T_0 is the initial chain anchor.
ChainStartsAtAnchor == t_history[1] = H0_T

\* Each subsequent T value is HmacExpand applied to (prk, T_{i-1}, info, i).
\* This captures the "every expand block depends on prk" claim: each T_i
\* is structurally a function of prk.
ExpandChainConsistent ==
    (phase = "expand" \/ phase = "done") =>
        \A k \in 1..expand_idx :
            t_history[k + 1] = HmacExpand[<<prk, t_history[k], InfoConst, k>>]

\* In extract phase the chain hasn't started.
ExtractPhaseEmpty ==
    phase = "extract" => t_history = <<H0_T>>

\* PRK is the extract output once extract has finished.
PrkDependsOnIkm ==
    (phase = "expand" \/ phase = "done") => prk = SaltIkmPrk

\* ---- Init ----------------------------------------------------------------

Init ==
    /\ phase = "extract"
    /\ prk = H0_T     \* initial value before ExtractStep
    /\ t_history = <<H0_T>>
    /\ expand_idx = 0

\* ---- Actions -------------------------------------------------------------

\* ExtractStep: derive PRK from (salt, IKM). Abstracted as setting PRK to
\* the SaltIkmPrk constant, then transitioning to expand phase.
ExtractStep ==
    /\ phase = "extract"
    /\ prk' = SaltIkmPrk
    /\ phase' = "expand"
    /\ UNCHANGED <<t_history, expand_idx>>

\* ExpandStep: advance the expand chain by one HMAC application.
ExpandStep ==
    /\ phase = "expand"
    /\ expand_idx < ExpandBlocks
    /\ LET next_t == HmacExpand[<<prk, t_history[Len(t_history)],
                                    InfoConst, expand_idx + 1>>]
       IN t_history' = Append(t_history, next_t)
    /\ expand_idx' = expand_idx + 1
    /\ UNCHANGED <<phase, prk>>

\* FinishExpand: all blocks produced, transition to done.
FinishExpand ==
    /\ phase = "expand"
    /\ expand_idx = ExpandBlocks
    /\ phase' = "done"
    /\ UNCHANGED <<prk, t_history, expand_idx>>

\* Terminal stutter.
Done ==
    /\ phase = "done"
    /\ UNCHANGED vars

Next ==
    \/ ExtractStep
    \/ ExpandStep
    \/ FinishExpand
    \/ Done

Spec == Init /\ [][Next]_vars

\* ---- Theorem (checked by TLC) --------------------------------------------

THEOREM Spec =>
    [](TypeInvariant /\ PhaseOrdering /\ ChainStartsAtAnchor
       /\ ExpandChainConsistent /\ ExtractPhaseEmpty /\ PrkDependsOnIkm)
====
