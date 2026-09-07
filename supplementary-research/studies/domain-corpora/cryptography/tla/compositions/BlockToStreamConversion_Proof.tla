---- MODULE BlockToStreamConversion_Proof ----
(***************************************************************************
  TLAPS proof of safety for the BlockToStreamConversion composition
  (CTR-mode).

  Discharges the THEOREM declared in BlockToStreamConversion.tla:
      Spec => [](TypeInvariant /\ CounterMonotonic
                                /\ UniqueCounters /\ OutputCorrect)

  Inductive strengthening: `CountersUsedEqualsRange ==
  counters_used = InitialCounter..(InitialCounter + next_block - 2)`.
  This captures the load-bearing structural fact: counters are used
  sequentially in InitialCounter..(InitialCounter + next_block - 2), with
  no gaps and no reuse. The strengthening implies UniqueCounters (the
  cardinality is exactly next_block - 1) and is needed so the new counter
  c = InitialCounter + next_block - 1 added by ProduceBlock is provably
  fresh (not in the prior range).

  This proof module artifact per the TLA+ study contract
 ***************************************************************************)
EXTENDS BlockToStreamConversion, Naturals, Sequences, FiniteSets, FiniteSetTheorems, TLAPS

ASSUME NumBlocksType      == NumBlocks      \in Nat /\ NumBlocks >= 1
ASSUME InitialCounterType == InitialCounter \in Nat

\* Helper: KeyValue lies in Key.
LEMMA KeyValueType == KeyValue \in Key
  BY DEF KeyValue, Key

\* Helper: BlockValue elements.
LEMMA BlockValueElements ==
    /\ b0 \in BlockValue
    /\ b1 \in BlockValue
    /\ b2 \in BlockValue
    /\ b3 \in BlockValue
  BY DEF BlockValue

\* Helper: plaintext_blocks[i] is in BlockValue for i in domain.
LEMMA PlaintextBlocksType ==
    \A i \in 1..NumBlocks : plaintext_blocks[i] \in BlockValue
  BY DEF plaintext_blocks, BlockValue

\* Helper: BlockTransform maps any (Key, CounterRange) into BlockValue.
LEMMA BlockTransformType ==
    \A c \in CounterRange :
        BlockTransform[<<KeyValue, c>>] \in BlockValue
  BY KeyValueType DEF BlockTransform, BlockValue, KeyValue, Key

\* Helper: Xor maps any (BlockValue, BlockValue) into BlockValue.
LEMMA XorType ==
    \A a \in BlockValue, b \in BlockValue : Xor[<<a, b>>] \in BlockValue
  BY DEF Xor, BlockValue

\* Strengthening: counters_used is the sequential range from InitialCounter
\* through InitialCounter + next_block - 2. Implies UniqueCounters and
\* implies the new counter is fresh on each ProduceBlock action.
CountersUsedEqualsRange ==
    counters_used = InitialCounter..(InitialCounter + next_block - 2)

\* Strengthening: keystream's domain matches counters_used.
KeystreamDomain == DOMAIN keystream = counters_used

\* Inductive invariant.
Inv == TypeInvariant /\ CounterMonotonic /\ UniqueCounters /\ OutputCorrect
       /\ CountersUsedEqualsRange /\ KeystreamDomain

(*-------------------------------------------------------------------------*)
(* Lemma: Init establishes the inductive invariant.                        *)
(*-------------------------------------------------------------------------*)
LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv
    OBVIOUS
  <1>1. TypeInvariant
    <2>1. next_block = 1                                    BY DEF Init
    <2>2. counters_used = {}                                BY DEF Init
    <2>3. ciphertext = <<>>                                 BY DEF Init
    <2>4. keystream \in [{} -> BlockValue]                  BY DEF Init
    <2> QED  BY <2>1, <2>2, <2>3, <2>4, NumBlocksType, InitialCounterType
              DEF TypeInvariant
  <1>2. CounterMonotonic
    BY DEF Init, CounterMonotonic
  <1>3. UniqueCounters
    <2>1. counters_used = {}                                BY DEF Init
    <2>2. next_block = 1                                    BY DEF Init
    <2> QED  BY <2>1, <2>2, FS_EmptySet DEF UniqueCounters
  <1>4. OutputCorrect
    \* 1..(next_block - 1) = 1..0 = {}; vacuous.
    BY DEF Init, OutputCorrect
  <1>5. CountersUsedEqualsRange
    \* InitialCounter..(InitialCounter - 1) = {}.
    BY InitialCounterType DEF Init, CountersUsedEqualsRange
  <1>6. KeystreamDomain
    BY DEF Init, KeystreamDomain
  <1> QED  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Inv

(*-------------------------------------------------------------------------*)
(* Lemma: every Next step preserves the inductive invariant.               *)
(*-------------------------------------------------------------------------*)
LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <1> USE DEF Inv, TypeInvariant, CounterMonotonic, UniqueCounters,
              OutputCorrect, CountersUsedEqualsRange, KeystreamDomain
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF vars
  <1>1. CASE ProduceBlock
    \* Extract post-state facts.
    <2>a. next_block <= NumBlocks                            BY <1>1 DEF ProduceBlock
    <2> DEFINE
        c  == InitialCounter + next_block - 1
        ks == BlockTransform[<<KeyValue, c>>]
        ct == Xor[<<plaintext_blocks[next_block], ks>>]
    <2>b. ciphertext' = Append(ciphertext, ct)               BY <1>1 DEF ProduceBlock
    <2>c. counters_used' = counters_used \cup {c}            BY <1>1 DEF ProduceBlock
    <2>d. keystream' = [d \in counters_used \cup {c} |->
                          IF d = c THEN ks ELSE keystream[d]]
      BY <1>1 DEF ProduceBlock
    <2>e. next_block' = next_block + 1                       BY <1>1 DEF ProduceBlock
    \* Stage 1: typing.
    <2>f. next_block \in 1..NumBlocks                        BY <2>a, NumBlocksType
    <2>g. c \in CounterRange
      BY <2>f, NumBlocksType, InitialCounterType DEF CounterRange
    <2>h. ks \in BlockValue                                  BY <2>g, BlockTransformType
    <2>i. plaintext_blocks[next_block] \in BlockValue        BY <2>f, PlaintextBlocksType
    <2>j. ct \in BlockValue                                  BY <2>i, <2>h, XorType
    <2>k. c \notin counters_used
      \* By CountersUsedEqualsRange, counters_used = InitialCounter..(InitialCounter + next_block - 2).
      \* c = InitialCounter + next_block - 1 > InitialCounter + next_block - 2, so c \notin range.
      BY <2>f, NumBlocksType, InitialCounterType
    <2>l. Cardinality(counters_used) = next_block - 1        OBVIOUS
    <2>m. IsFiniteSet(counters_used)
      BY <2>f, NumBlocksType, InitialCounterType, FS_Interval
    <2>n. Cardinality(counters_used \cup {c}) = next_block
      <3>1. IsFiniteSet({c})                                 BY FS_Singleton
      <3>2. Cardinality(counters_used \cup {c}) = Cardinality(counters_used) + 1
        BY <2>k, <2>m, <3>1, FS_AddElement
      <3> QED  BY <2>l, <3>2, NumBlocksType, <2>f
    \* Stage 2: invariant preservation.
    <2>1. TypeInvariant'
      <3>1. next_block' \in 1..NumBlocks + 1
        BY <2>a, <2>e, NumBlocksType
      <3>2. counters_used' \subseteq InitialCounter..(InitialCounter + NumBlocks)
        <4>1. counters_used \subseteq InitialCounter..(InitialCounter + NumBlocks)
          OBVIOUS
        <4>2. c \in InitialCounter..(InitialCounter + NumBlocks)
          BY <2>f, NumBlocksType, InitialCounterType
        <4> QED  BY <2>c, <4>1, <4>2
      <3>3. ciphertext' \in Seq(BlockValue)
        <4>1. ciphertext \in Seq(BlockValue)                 OBVIOUS
        <4> QED  BY <2>b, <2>j, <4>1
      <3>4. keystream' \in [counters_used' -> BlockValue]
        <4>1. \A d \in counters_used \cup {c} :
                  (IF d = c THEN ks ELSE keystream[d]) \in BlockValue
          <5> SUFFICES ASSUME NEW d \in counters_used \cup {c}
                       PROVE  (IF d = c THEN ks ELSE keystream[d]) \in BlockValue
            OBVIOUS
          <5>1. CASE d = c
            BY <2>h, <5>1
          <5>2. CASE d /= c
            <6>1. d \in counters_used                        BY <5>2
            <6>2. d \in DOMAIN keystream                     BY <6>1
            <6>3. keystream[d] \in BlockValue
              BY <6>2  \* keystream \in [counters_used -> BlockValue]
            <6> QED  BY <5>2, <6>3
          <5> QED  BY <5>1, <5>2
        <4> QED  BY <2>c, <2>d, <4>1
      <3>5. Len(ciphertext') = next_block' - 1
        <4>1. Len(ciphertext) = next_block - 1               OBVIOUS
        <4>2. Len(ciphertext') = Len(ciphertext) + 1         BY <2>b, <2>j
        <4> QED  BY <4>1, <4>2, <2>e, NumBlocksType, <2>f
      <3> QED  BY <3>1, <3>2, <3>3, <3>4, <3>5
    <2>2. CounterMonotonic'
      <3> SUFFICES ASSUME NEW cc \in counters_used'
                   PROVE  /\ cc >= InitialCounter
                          /\ cc < InitialCounter + next_block'
        BY DEF CounterMonotonic
      <3>1. CASE cc \in counters_used
        <4>1. cc >= InitialCounter /\ cc < InitialCounter + next_block
          BY <3>1
        <4>2. cc \in InitialCounter..(InitialCounter + NumBlocks)
          BY <3>1  \* counters_used \subseteq InitialCounter..(InitialCounter + NumBlocks) (TypeInvariant)
        <4>3. cc \in Nat
          BY <4>2, NumBlocksType, InitialCounterType
        <4> QED  BY <4>1, <4>3, <2>e, NumBlocksType, <2>f, InitialCounterType
      <3>2. CASE cc = c
        <4>1. cc = InitialCounter + next_block - 1
          BY <3>2
        <4> QED  BY <4>1, <2>e, NumBlocksType, <2>f, InitialCounterType
      <3> QED  BY <2>c, <3>1, <3>2
    <2>3. UniqueCounters'
      BY <2>c, <2>e, <2>n DEF UniqueCounters
    <2>4. OutputCorrect'
      <3> SUFFICES ASSUME NEW i \in 1..(next_block' - 1)
                   PROVE  LET cc  == InitialCounter + i - 1
                              kss == BlockTransform[<<KeyValue, cc>>]
                          IN  /\ ciphertext'[i] = Xor[<<plaintext_blocks[i], kss>>]
                              /\ cc \in counters_used'
                              /\ keystream'[cc] = kss
        BY DEF OutputCorrect
      <3>1. i \in 1..next_block                               BY <2>e, NumBlocksType, <2>f
      <3>A. CASE i \in 1..(next_block - 1)
        \* Old index: ciphertext'[i] = ciphertext[i] (Append prefix), counters_used preserves,
        \* keystream'[cc] = keystream[cc] (cc != c since cc < InitialCounter + next_block - 1 = c).
        <4> DEFINE
            cc  == InitialCounter + i - 1
            kss == BlockTransform[<<KeyValue, cc>>]
        <4>1. ciphertext[i] = Xor[<<plaintext_blocks[i], kss>>]
              /\ cc \in counters_used
              /\ keystream[cc] = kss
          BY <3>A DEF OutputCorrect
        <4>2. Len(ciphertext) = next_block - 1               OBVIOUS
        <4>3. i \in 1..Len(ciphertext)                       BY <3>A, <4>2
        <4>4. ciphertext'[i] = ciphertext[i]
          BY <2>b, <2>j, <4>3
        <4>5. cc \in counters_used'                          BY <2>c, <4>1
        <4>6. cc /= c
          BY <3>A, <2>f, NumBlocksType, InitialCounterType
        <4>7. keystream'[cc] = keystream[cc]
          <5>1. cc \in counters_used \cup {c}                BY <4>1
          <5>2. (IF cc = c THEN ks ELSE keystream[cc]) = keystream[cc]
            BY <4>6
          <5> QED  BY <2>d, <5>1, <5>2
        <4> QED  BY <4>1, <4>4, <4>5, <4>7
      <3>B. CASE i = next_block
        \* New index: ciphertext'[next_block] = ct, cc = c.
        <4> DEFINE
            cc  == InitialCounter + i - 1
            kss == BlockTransform[<<KeyValue, cc>>]
        <4>1. cc = c                                          BY <3>B
        <4>2. kss = ks                                        BY <4>1
        <4>3. Len(ciphertext) = next_block - 1               OBVIOUS
        <4>4. Len(ciphertext) + 1 = next_block               BY <4>3, NumBlocksType, <2>f
        <4>5. i = Len(ciphertext) + 1                        BY <3>B, <4>4
        <4>6. ciphertext'[i] = ct
          BY <2>b, <2>j, <4>5
        <4>7. ct = Xor[<<plaintext_blocks[next_block], ks>>]  OBVIOUS
        <4>8. ciphertext'[i] = Xor[<<plaintext_blocks[i], kss>>]
          BY <4>2, <4>6, <4>7, <3>B
        <4>9. cc \in counters_used'                          BY <4>1, <2>c
        <4>10. keystream'[cc] = ks
          <5>1. cc \in counters_used \cup {c}                BY <4>1
          <5>2. (IF cc = c THEN ks ELSE keystream[cc]) = ks
            BY <4>1
          <5> QED  BY <2>d, <5>1, <5>2
        <4>11. keystream'[cc] = kss
          BY <4>2, <4>10
        <4> QED  BY <4>8, <4>9, <4>11
      <3> QED  BY <3>1, <2>e, <3>A, <3>B, NumBlocksType, <2>f
    <2>5. CountersUsedEqualsRange'
      <3>1. counters_used' = InitialCounter..(InitialCounter + next_block - 1)
        <4>1. counters_used = InitialCounter..(InitialCounter + next_block - 2)
          OBVIOUS
        <4>2. counters_used' = InitialCounter..(InitialCounter + next_block - 2) \cup {c}
          BY <2>c, <4>1
        <4>3. InitialCounter..(InitialCounter + next_block - 2) \cup {c}
                = InitialCounter..(InitialCounter + next_block - 1)
          BY <2>f, NumBlocksType, InitialCounterType
        <4> QED  BY <4>2, <4>3
      <3>2. InitialCounter + next_block - 1 = InitialCounter + next_block' - 2
        BY <2>e
      <3> QED  BY <3>1, <3>2 DEF CountersUsedEqualsRange
    <2>6. KeystreamDomain'
      BY <2>c, <2>d
    <2> QED  BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6
  <1>2. CASE Done
    BY <1>2 DEF Done, vars
  <1>3. CASE Next
    BY <1>3, <1>1, <1>2 DEF Next
  <1> QED  BY <1>0, <1>3

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

THEOREM CounterMonotonicSafety == Spec => []CounterMonotonic
  BY Safety, PTL DEF Inv

THEOREM UniqueCountersSafety == Spec => []UniqueCounters
  BY Safety, PTL DEF Inv

THEOREM OutputCorrectSafety == Spec => []OutputCorrect
  BY Safety, PTL DEF Inv

====
