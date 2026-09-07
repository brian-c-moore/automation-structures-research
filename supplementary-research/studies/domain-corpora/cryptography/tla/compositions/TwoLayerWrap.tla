---- MODULE TwoLayerWrap ----
(*
  Two-layer wrap.

  HMAC's structural pattern: a hash compression function is applied twice
  in sequence, with the output of the first invocation fed into the second
  along with an "outer key" prefix. The first invocation processes the
  "inner key" prefix followed by the message; the second processes the
  outer key prefix followed by the inner hash output. The two prefixes
  differ (in HMAC, K XOR ipad vs K XOR opad); modeled abstractly here as
  two distinct prefix sequences `InnerKey` and `OuterKey`.

  Canonical example: HMAC-SHA-256. The pattern also appears in HMAC over
  other hash functions, NMAC's two-layer construction, and any
  prefix-then-suffix MAC.

  Build requirements demonstrated: ResourceRegistry (hash state) +
    TraversalEngine (over input sequence within each phase) +
    ActuationPass (per-block Compress call). The Compress function is
    uninterpreted cryptographic content. Sequential composition of two
    iterated-transformations (the IteratedTransformationOverChainedState
    pattern), with the output of phase 1 flowing into the input of phase 2.

  Safety claims:
    PhaseOrdering — outer phase begins only after inner phase finishes.
    InnerChainConsistent — inner history's k-th step is Compress applied
      to the (k-1)-th state and the k-th inner input (InnerKey then Msg).
    OuterChainConsistent — outer history's k-th step is Compress applied
      to the (k-1)-th state and the k-th outer input (OuterKey then
      inner_result).
    InnerResultSnapshot — once captured, inner_result equals the last
      inner-history state (the inner hash output).

  The length-extension impossibility of HMAC is structural: the outer
  Compress wraps the inner hash output with a key-derived prefix that an
  attacker cannot mimic without knowing the key. This spec captures the
  structural property; the cryptographic claim follows from any Compress
  satisfying first-preimage resistance.

  Bounded parameters per the study definition: KeyLen = 2, MsgLen = 2. Exhaustive.

  Expected outcome: No error has been found  (PASS).
*)
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    h0, h1,             \* hash-state model values
    kb0, kb1,           \* key-byte model values
    mb0, mb1,           \* msg-byte model values
    KeyLen,             \* number of key-prefix blocks per phase
    MsgLen              \* number of msg blocks (inner phase suffix)

ASSUME KeyLen \in Nat /\ KeyLen >= 1
ASSUME MsgLen \in Nat /\ MsgLen >= 1

\* ── Fixed topology (the .cfg supplies only model-value constants) ─────────
\* Following MemoizationComposition.tla's idiom (topology + content inline;
\* .cfg holds only model values).
HashState == {h0, h1}
KeyByte   == {kb0, kb1}
MsgByte   == {mb0, mb1}

\* Block: the input alphabet for Compress. Spans hash-state values (for the
\* "inner-result is fed into outer Compress" case), key bytes, and msg bytes.
Block == HashState \cup KeyByte \cup MsgByte

H0 == h0  \* initial hash state

\* InnerKey: the inner prefix sequence (K XOR ipad in HMAC).
InnerKey ==
    [k \in 1..KeyLen |->
        IF k = 1 THEN kb0 ELSE kb1]

\* OuterKey: the outer prefix sequence (K XOR opad in HMAC). Differs from
\* InnerKey so the two phases are not interchangeable.
OuterKey ==
    [k \in 1..KeyLen |->
        IF k = 1 THEN kb1 ELSE kb0]

\* Msg: the message bytes.
Msg ==
    [k \in 1..MsgLen |->
        IF k = 1 THEN mb0 ELSE mb1]

\* Compress: HashState \X Block -> HashState.  Deterministic; the structural
\* correctness of the pattern is independent of the particular content.
Compress ==
    [p \in HashState \X Block |->
        IF      p = <<h0, h0>>  THEN h1
        ELSE IF p = <<h0, h1>>  THEN h0
        ELSE IF p = <<h0, kb0>> THEN h1
        ELSE IF p = <<h0, kb1>> THEN h0
        ELSE IF p = <<h0, mb0>> THEN h1
        ELSE IF p = <<h0, mb1>> THEN h0
        ELSE IF p = <<h1, h0>>  THEN h0
        ELSE IF p = <<h1, h1>>  THEN h1
        ELSE IF p = <<h1, kb0>> THEN h0
        ELSE IF p = <<h1, kb1>> THEN h1
        ELSE IF p = <<h1, mb0>> THEN h0
        ELSE                         h1]

\* InnerInputAt: the k-th input fed into the inner phase. k in 1..KeyLen
\* yields InnerKey[k]; k in KeyLen+1..KeyLen+MsgLen yields Msg[k - KeyLen].
InnerInputAt(k) ==
    IF k <= KeyLen THEN InnerKey[k] ELSE Msg[k - KeyLen]

\* InnerInputLen: total number of inner-phase Compress steps.
InnerInputLen == KeyLen + MsgLen

\* OuterInputAt: the k-th input fed into the outer phase. k in 1..KeyLen
\* yields OuterKey[k]; k = KeyLen+1 yields inner_result (the variable).
\* Since inner_result is a variable, this is a per-step lookup, not a
\* CONSTANT-defined function.

\* OuterInputLen: total number of outer-phase Compress steps.
OuterInputLen == KeyLen + 1

VARIABLES
    state,             \* current Compress state (active phase)
    phase,             \* "inner" / "outer" / "done"
    inner_idx,         \* progress in inner phase (0..InnerInputLen)
    outer_idx,         \* progress in outer phase (0..OuterInputLen)
    inner_history,     \* chain of states visited in inner phase
    outer_history,     \* chain of states visited in outer phase
    inner_result       \* saved hash result of inner phase; H0 before FinishInner

vars == <<state, phase, inner_idx, outer_idx,
          inner_history, outer_history, inner_result>>

\* ---- Type invariant ------------------------------------------------------

TypeInvariant ==
    /\ state \in HashState
    /\ phase \in {"inner", "outer", "done"}
    /\ inner_idx \in 0..InnerInputLen
    /\ outer_idx \in 0..OuterInputLen
    /\ inner_history \in Seq(HashState)
    /\ outer_history \in Seq(HashState)
    /\ inner_result \in HashState
    /\ Len(inner_history) = inner_idx + 1
    /\ Len(outer_history) = outer_idx + 1

\* ---- Safety invariants ---------------------------------------------------

\* The phases progress in order: outer begins only after inner is finished.
PhaseOrdering ==
    /\ (phase = "outer" \/ phase = "done") => inner_idx = InnerInputLen
    /\ phase = "done" => outer_idx = OuterInputLen
    /\ phase = "inner" => outer_idx = 0
    /\ phase = "inner" => outer_history = <<H0>>

\* Both histories start at H0.
HistoriesStartAtH0 ==
    /\ inner_history[1] = H0
    /\ outer_history[1] = H0

\* Inner-phase chain: each consecutive pair in inner_history is linked by
\* Compress applied to the corresponding inner input.
InnerChainConsistent ==
    \A k \in 1..inner_idx :
        inner_history[k + 1] = Compress[<<inner_history[k], InnerInputAt(k)>>]

\* Outer-phase chain: each consecutive pair in outer_history is linked by
\* Compress applied to the corresponding outer input. For k <= KeyLen the
\* input is OuterKey[k]; for k = KeyLen + 1 the input is inner_result.
OuterChainConsistent ==
    \A k \in 1..outer_idx :
        outer_history[k + 1] = Compress[<<outer_history[k],
                                          IF k <= KeyLen THEN OuterKey[k]
                                          ELSE inner_result>>]

\* Once captured, inner_result equals the last inner-history state — the
\* inner hash's final output.
InnerResultSnapshot ==
    (phase = "outer" \/ phase = "done") =>
        inner_result = inner_history[Len(inner_history)]

\* The current state matches the active phase's history-tail.
ChainedStateCorrect ==
    /\ phase = "inner" => state = inner_history[Len(inner_history)]
    /\ phase = "outer" => state = outer_history[Len(outer_history)]

\* ---- Init ----------------------------------------------------------------

Init ==
    /\ state = H0
    /\ phase = "inner"
    /\ inner_idx = 0
    /\ outer_idx = 0
    /\ inner_history = <<H0>>
    /\ outer_history = <<H0>>
    /\ inner_result = H0   \* initial value before FinishInner

\* ---- Actions -------------------------------------------------------------

\* Advance the inner-phase chain by one Compress step.
InnerStep ==
    /\ phase = "inner"
    /\ inner_idx < InnerInputLen
    /\ state' = Compress[<<state, InnerInputAt(inner_idx + 1)>>]
    /\ inner_idx' = inner_idx + 1
    /\ inner_history' = Append(inner_history, state')
    /\ UNCHANGED <<phase, outer_idx, outer_history, inner_result>>

\* Capture the inner result and transition to outer phase.
FinishInner ==
    /\ phase = "inner"
    /\ inner_idx = InnerInputLen
    /\ inner_result' = state
    /\ state' = H0
    /\ phase' = "outer"
    /\ UNCHANGED <<inner_idx, outer_idx, inner_history, outer_history>>

\* Advance the outer-phase chain by one Compress step.
OuterStep ==
    /\ phase = "outer"
    /\ outer_idx < OuterInputLen
    /\ LET input == IF outer_idx + 1 <= KeyLen THEN OuterKey[outer_idx + 1]
                                                ELSE inner_result
       IN state' = Compress[<<state, input>>]
    /\ outer_idx' = outer_idx + 1
    /\ outer_history' = Append(outer_history, state')
    /\ UNCHANGED <<phase, inner_idx, inner_history, inner_result>>

\* Transition from outer phase to done.
FinishOuter ==
    /\ phase = "outer"
    /\ outer_idx = OuterInputLen
    /\ phase' = "done"
    /\ UNCHANGED <<state, inner_idx, outer_idx,
                   inner_history, outer_history, inner_result>>

\* Terminal stutter.
Done ==
    /\ phase = "done"
    /\ UNCHANGED vars

Next ==
    \/ InnerStep
    \/ FinishInner
    \/ OuterStep
    \/ FinishOuter
    \/ Done

Spec == Init /\ [][Next]_vars

\* ---- Theorem (checked by TLC) --------------------------------------------

THEOREM Spec =>
    [](TypeInvariant /\ PhaseOrdering /\ HistoriesStartAtH0
       /\ InnerChainConsistent /\ OuterChainConsistent
       /\ InnerResultSnapshot /\ ChainedStateCorrect)
====
