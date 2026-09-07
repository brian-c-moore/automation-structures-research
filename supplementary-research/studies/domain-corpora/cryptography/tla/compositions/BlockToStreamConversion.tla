---- MODULE BlockToStreamConversion ----
(*
  Block-to-stream conversion.

  A composition that wraps a fixed-size block transformation with a
  counter-driven TraversalEngine to produce arbitrary-length output.
  The counter parameterisation makes the block iteration Tree-shaped
  rather than Linear, enabling per-block Fork-join parallelism.

  Canonical example: AES-CTR. ChaCha20 as a stream cipher uses the same
  composition with a different underlying transformation. The pattern
  appears in any counter-mode encryption (CTR, GCM's encryption phase,
  CCM's encryption phase) and in counter-based pseudo-random function
  constructions.

  Build requirements demonstrated:
    ResourceRegistry (key + counter + keystream-block-per-counter +
      plaintext + ciphertext).
    TraversalEngine over the input blocks (counter-driven; the block
      iteration is Tree-shaped because each block's keystream depends
      only on (key, counter)).
    ActuationPass per BlockTransform call.
    Reduction (XOR) of keystream with plaintext.

  The BlockTransform function is uninterpreted cryptographic content —
  the structural pattern is parametric over it. Same content
  abstraction the iterated-transformation spec uses.

  Safety claims:
    CounterMonotonic — counters are used in strictly increasing order,
      starting from `InitialCounter`.
    UniqueCounters — no counter value is used twice (the load-bearing
      property: reusing a (key, counter) pair would compromise security).
    OutputCorrect — each ciphertext block equals XOR of the
      corresponding plaintext block and BlockTransform(key, counter).

  Bounded parameters per the study definition: Counter ∈ 0..3, block size
  small. Exhaustive.

  Expected outcome: No error has been found  (PASS).
*)
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    k_alpha,              \* key model value
    b0, b1, b2, b3,       \* block-value model values
    NumBlocks,            \* number of plaintext blocks (>= 1)
    InitialCounter        \* starting counter value (Nat)

ASSUME NumBlocks \in Nat /\ NumBlocks >= 1
ASSUME InitialCounter \in Nat

\* ── Fixed topology (the .cfg supplies only model-value constants) ─────────
\* The pattern's correctness is structural and parametric over any concrete
\* Key / KeyValue / BlockValue / plaintext_blocks / BlockTransform / Xor
\* choice; this one is fixed here so TLC can exhaustively check the
\* composition. Defined inside the .tla following
\* MemoizationComposition.tla's idiom (topology + content inline; .cfg holds
\* only model values).
Key        == {k_alpha}
KeyValue   == k_alpha
BlockValue == {b0, b1, b2, b3}

\* plaintext_blocks: 1..NumBlocks -> BlockValue.
\* Nested IF-THEN-ELSE: the SMT backend does not translate CASE arms.
plaintext_blocks ==
    [i \in 1..NumBlocks |->
        IF      i = 1 THEN b1
        ELSE IF i = 2 THEN b2
        ELSE IF i = 3 THEN b3
        ELSE              b0]

\* CounterRange: the counter values actually accessed by the spec.
\* Used to give BlockTransform a finite (and well-defined) domain.
CounterRange == InitialCounter..(InitialCounter + NumBlocks - 1)

\* BlockTransform: Key \X CounterRange -> BlockValue.
\* Deterministic function (key, counter) -> block.
BlockTransform ==
    [p \in Key \X CounterRange |->
        IF      p = <<k_alpha, 0>> THEN b1
        ELSE IF p = <<k_alpha, 1>> THEN b3
        ELSE IF p = <<k_alpha, 2>> THEN b0
        ELSE IF p = <<k_alpha, 3>> THEN b2
        ELSE                            b1]

\* Xor: BlockValue \X BlockValue -> BlockValue.
\* Deterministic involution (a XOR a = identity).
Xor ==
    [p \in BlockValue \X BlockValue |->
        IF      p = <<b0, b0>> THEN b0
        ELSE IF p = <<b0, b1>> THEN b1
        ELSE IF p = <<b0, b2>> THEN b2
        ELSE IF p = <<b0, b3>> THEN b3
        ELSE IF p = <<b1, b0>> THEN b1
        ELSE IF p = <<b1, b1>> THEN b0
        ELSE IF p = <<b1, b2>> THEN b3
        ELSE IF p = <<b1, b3>> THEN b2
        ELSE IF p = <<b2, b0>> THEN b2
        ELSE IF p = <<b2, b1>> THEN b3
        ELSE IF p = <<b2, b2>> THEN b0
        ELSE IF p = <<b2, b3>> THEN b1
        ELSE IF p = <<b3, b0>> THEN b3
        ELSE IF p = <<b3, b1>> THEN b2
        ELSE IF p = <<b3, b2>> THEN b1
        ELSE                        b0]

VARIABLES
    next_block,            \* TraversalEngine: index of next block to produce
                           \*                  (1..NumBlocks + 1)
    counters_used,         \* set of counter values used so far
    ciphertext,            \* sequence of produced ciphertext blocks
    keystream              \* function: counter value -> keystream block
                           \*           (defined only for used counters)

vars == <<next_block, counters_used, ciphertext, keystream>>

\* ---- Type invariant ------------------------------------------------------

TypeInvariant ==
    /\ next_block \in 1..NumBlocks + 1
    /\ counters_used \subseteq InitialCounter..(InitialCounter + NumBlocks)
    /\ ciphertext \in Seq(BlockValue)
    /\ keystream \in [counters_used -> BlockValue]
    /\ Len(ciphertext) = next_block - 1

\* ---- Safety invariants ---------------------------------------------------

\* Every counter value used is in the expected sequential range.
CounterMonotonic ==
    \A c \in counters_used :
        /\ c >= InitialCounter
        /\ c < InitialCounter + next_block

\* The set of used counters never has duplicates (set semantics give this
\* by construction; the invariant pins it as a checked property).
UniqueCounters ==
    Cardinality(counters_used) = next_block - 1

\* Each ciphertext block i = Xor(plaintext_blocks[i], BlockTransform(key, counter_i))
\* where counter_i = InitialCounter + i - 1.
OutputCorrect ==
    \A i \in 1..(next_block - 1) :
        LET c == InitialCounter + i - 1
            ks == BlockTransform[<<KeyValue, c>>]
        IN  ciphertext[i] = Xor[<<plaintext_blocks[i], ks>>]
            /\ c \in counters_used
            /\ keystream[c] = ks

\* ---- Init ----------------------------------------------------------------

Init ==
    /\ next_block = 1
    /\ counters_used = {}
    /\ ciphertext = <<>>
    /\ keystream = [c \in {} |-> b0]   \* empty function; body unreachable

\* ---- Actions -------------------------------------------------------------

\* ResourceRegistry update + ActuationPass: produce the next ciphertext block.
ProduceBlock ==
    /\ next_block <= NumBlocks
    /\ LET c  == InitialCounter + next_block - 1
           ks == BlockTransform[<<KeyValue, c>>]
           ct == Xor[<<plaintext_blocks[next_block], ks>>]
       IN  /\ ciphertext'      = Append(ciphertext, ct)
           /\ counters_used'   = counters_used \cup {c}
           /\ keystream'       = [d \in counters_used \cup {c} |->
                                    IF d = c THEN ks ELSE keystream[d]]
           /\ next_block'      = next_block + 1

\* Terminal state: all blocks produced, stutter.
Done ==
    /\ next_block = NumBlocks + 1
    /\ UNCHANGED vars

Next ==
    \/ ProduceBlock
    \/ Done

Spec == Init /\ [][Next]_vars

\* ---- Theorem (checked by TLC) --------------------------------------------

THEOREM Spec =>
    [](TypeInvariant /\ CounterMonotonic /\ UniqueCounters /\ OutputCorrect)
====
