---- MODULE IteratedTransformationOverChainedState ----
(*
  Iterated transformation over chained state.

  The dominant cryptographic composition pattern. A fixed-size state is
  held in a ResourceRegistry. A TraversalEngine walks an input sequence
  (rounds, blocks, message-schedule positions). At each step, an
  ActuationPass applies a fixed transformation to the state based on
  the current input element. The state's final value is the output.

  Models the round structure of SHA-256, SHA-3 absorb/squeeze, AES,
  ChaCha20, HMAC, HKDF-expand, PBKDF2, RSA, Ed25519, X25519. Twelve of
  the fifteen corpus algorithms instantiate this pattern.

  Build requirements demonstrated: ResourceRegistry + TraversalEngine
    + ActuationPass + (optional) Sampler. The RoundFn is uninterpreted
    cryptographic content; the pattern is parametric over it. The
    optional Sampler participant is exercised in the
    randomness-driven instantiation (RSA-PSS salt, Miller-Rabin
    witnesses, rejection sampling); absent from the deterministic
    instantiations. The five-primitive overlap with the classical
    corpus plus Sampler-asymmetric-to-cryptography is the substantive
    cross-corpus difference.

  Primitive references (semantics re-stated inline, sources cited):
    ResourceRegistry: state held as <<position, value>> pairs.
      Source: primitives/ResourceRegistry.tla
    TraversalEngine: bounded iteration over chain index 0..ChainLength.
      Source: primitives/TraversalEngine.tla
    ActuationPass: per-step state update via RoundFn.
      Source: primitives/ActuationPass.tla

  Expected outcome: No error has been found  (PASS).
*)
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    s0, s1, s2,   \* state model values
    x1, x2, x3,   \* input model values
    ChainLength   \* bound on the iteration (e.g. 64 for SHA-256)

ASSUME ChainLength \in Nat /\ ChainLength >= 1

\* ── Fixed topology (the .cfg supplies only model-value constants) ─────────
\* The pattern's correctness is structural and parametric over any concrete
\* State / Input / InitialState / RoundFn / inputs choice; this one is fixed
\* here so TLC can exhaustively check the composition. Defined inside the
\* .tla following MemoizationComposition.tla's idiom (topology + content
\* inline; .cfg holds only model values).
State        == {s0, s1, s2}
Input        == {x1, x2, x3}
InitialState == s0

\* RoundFn: State \X Input -> State.  Deterministic mixing table.
\* Encoded as nested IF-THEN-ELSE rather than CASE so the SMT backend can
\* translate it during TLAPS lift: the Apalache/Z3 backends do not translate
\* CASE arms even with OTHER, while nested IF-THEN-ELSE totalizes cleanly.
RoundFn ==
    [p \in State \X Input |->
        IF      p = <<s0, x1>> THEN s1
        ELSE IF p = <<s0, x2>> THEN s2
        ELSE IF p = <<s0, x3>> THEN s0
        ELSE IF p = <<s1, x1>> THEN s2
        ELSE IF p = <<s1, x2>> THEN s0
        ELSE IF p = <<s1, x3>> THEN s1
        ELSE IF p = <<s2, x1>> THEN s0
        ELSE IF p = <<s2, x2>> THEN s1
        ELSE                        s2]

\* inputs: 1..ChainLength -> Input.  Chosen to exercise all three
\* RoundFn columns over the 4-step chain.  Nested IF-THEN-ELSE for the same
\* reason as RoundFn above.
inputs ==
    [k \in 1..ChainLength |->
        IF      k = 1 THEN x1
        ELSE IF k = 2 THEN x2
        ELSE IF k = 3 THEN x3
        ELSE              x1]

VARIABLES
    state,         \* ResourceRegistry: the current state value
    i,             \* TraversalEngine: the current chain index
    history        \* sequence of states visited (auxiliary, for the invariant)

vars == <<state, i, history>>

\* ---- Type invariant ------------------------------------------------------

TypeInvariant ==
    /\ state \in State
    /\ i \in 0..ChainLength
    /\ history \in Seq(State)
    /\ Len(history) = i + 1

\* ---- Safety invariants ---------------------------------------------------
\*
\* The chain's correctness is expressed via the history sequence itself,
\* using index-based reasoning over RoundFn, the idiom AuditSink.tla uses for
\* chain-integrity invariants. A recursive function fixpoint operator
\* `ExpectedAfter[k \in 0..ChainLength] == ...` would express the same thing
\* and clears TLC, but TLAPS 1.5.0's SMT backend does not unfold recursive
\* function fixpoints inside BY clauses. The non-recursive
\* sequence-of-states formulation below is equivalent and does lift.

\* The first history entry is the initial state.
HistoryStartsAtInit ==
    history[1] = InitialState

\* The last history entry is the current state. This is the central
\* correctness claim of the pattern, restated in non-recursive form.
ChainedStateCorrect ==
    state = history[Len(history)]

\* Each subsequent history entry is RoundFn applied to the previous
\* entry and the corresponding input. The iterated transformation
\* produces the unique sequence of states determined by RoundFn
\* applied step-by-step over the input prefix.
HistoryConsistent ==
    \A k \in 1..i : history[k + 1] = RoundFn[<<history[k], inputs[k]>>]

\* ---- Init ----------------------------------------------------------------

Init ==
    /\ state = InitialState
    /\ i = 0
    /\ history = <<InitialState>>

\* ---- Actions -------------------------------------------------------------

\* TraversalEngine + ActuationPass: advance by one round.
\* Guard: there is still input to consume.
Step ==
    /\ i < ChainLength
    /\ state' = RoundFn[<<state, inputs[i + 1]>>]
    /\ i' = i + 1
    /\ history' = Append(history, state')

\* Terminal: chain consumed, stutter.
Done ==
    /\ i = ChainLength
    /\ UNCHANGED vars

Next ==
    \/ Step
    \/ Done

Spec == Init /\ [][Next]_vars

\* ---- Theorem (checked by TLC) --------------------------------------------

THEOREM Spec => [](TypeInvariant /\ HistoryStartsAtInit
                                 /\ ChainedStateCorrect /\ HistoryConsistent)
====
