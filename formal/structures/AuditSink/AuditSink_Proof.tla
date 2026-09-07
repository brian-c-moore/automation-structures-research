---- MODULE AuditSink_Proof ----
(***************************************************************************
  Safety proof for AuditSink:
      Spec => [](ChainIntegrity /\ HashConsistency /\ HashBindsContent)

  ChainIntegrity is not inductive alone: preservation across Record(op)
  requires the HashConsistency relation
  last_hash = log[Len(log)].hash. Inv therefore combines the record shape,
  the carrier bounds, and all three safety invariants.
 ***************************************************************************)
EXTENDS AuditSink, Naturals, Sequences, TLAPS

\* Constants assumed well-formed by the AuditSink.cfg (Operations is a finite
\* set of model values; MaxLogLen is a natural number).
ASSUME MaxLogLenType == MaxLogLen \in Nat

\* HashType supplies the result type of the uninterpreted Hash operator.
ASSUME HashType == \A p \in Nat, op \in Operations : Hash(p, op) \in Nat

\* HashCR is an external cryptographic premise. TamperEvident is conditional
\* on this injectivity property; the module does not establish it for a
\* concrete hash function.
ASSUME HashCR ==
    \A p1, p2 \in Nat, o1, o2 \in Operations :
        Hash(p1, o1) = Hash(p2, o2) => (p1 = p2 /\ o1 = o2)

\* Shape of a log entry. Apalache-friendly record type; matches the entry
\* constructed in Record(op).
LogEntry == [operation : Operations, prev_hash : Nat, hash : Nat]

\* Inductive strengthening. Adds Seq(LogEntry) to TypeInvariant so the
\* per-index field accesses in ChainIntegrity, HashConsistency and
\* HashBindsContent are well-typed; conjoins all three safety invariants,
\* which is what lets the ChainIntegrity step use HashConsistency.
Inv ==
    /\ log \in Seq(LogEntry)
    /\ last_hash \in Nat
    /\ Len(log) <= MaxLogLen
    /\ ChainIntegrity
    /\ HashConsistency
    /\ HashBindsContent

\* Lemma 1: Init establishes the inductive invariant.
LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv
    OBVIOUS
  <1>1. log \in Seq(LogEntry)
    BY DEF Init, LogEntry
  <1>2. last_hash \in Nat
    BY DEF Init
  <1>3. Len(log) <= MaxLogLen
    BY MaxLogLenType DEF Init
  <1>4. ChainIntegrity
    \* log = <<>>, so 2..Len(log) = 2..0 = {}; the universal is vacuous.
    BY DEF Init, ChainIntegrity
  <1>5. HashConsistency
    BY DEF Init, HashConsistency
  <1>6. HashBindsContent
    \* log = <<>>, so 1..Len(log) = 1..0 = {}; the universal is vacuous.
    BY DEF Init, HashBindsContent
  <1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Inv

\* Lemma 2: every Next step preserves the inductive invariant.
LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <1>1. CASE UNCHANGED vars
    BY <1>1 DEF Inv, vars, ChainIntegrity, HashConsistency, HashBindsContent
  <1>2. CASE Next
    <2> SUFFICES ASSUME NEW op \in Operations, Record(op)
                 PROVE Inv'
      BY <1>2 DEF Next
    \* Names for the new state.
    <2> DEFINE
      new_hash == Hash(last_hash, op)
      entry == [operation |-> op, prev_hash |-> last_hash, hash |-> new_hash]
    <2>a. log' = Append(log, entry) /\ last_hash' = new_hash
      BY DEF Record
    <2>b. Len(log) < MaxLogLen
      BY DEF Record
    <2>c. log \in Seq(LogEntry) /\ last_hash \in Nat /\ ChainIntegrity /\ HashConsistency
            /\ HashBindsContent
      BY DEF Inv
    <2>d. new_hash \in Nat
      BY <2>c, HashType
    <2>e. entry \in LogEntry
      BY <2>c, <2>d DEF LogEntry
    \* TypeInvariant components.
    <2>1. log' \in Seq(LogEntry)
      BY <2>a, <2>c, <2>e
    <2>2. last_hash' \in Nat
      BY <2>a, <2>d
    <2>3. Len(log') <= MaxLogLen
      BY <2>a, <2>b, <2>c, MaxLogLenType
    \* ChainIntegrity is preserved.
    <2>4. ChainIntegrity'
      <3> SUFFICES ASSUME NEW i \in 2..Len(log')
                   PROVE log'[i].prev_hash = log'[i-1].hash
        BY DEF ChainIntegrity
      <3>1. Len(log') = Len(log) + 1
        BY <2>a, <2>c
      <3>2. CASE i \in 2..Len(log)
        \* Old pair: both entries are in the original log; inductive hyp.
        <4>1. log'[i] = log[i] /\ log'[i-1] = log[i-1]
          BY <2>a, <2>c, <3>2
        <4> QED BY <3>2, <4>1, <2>c DEF ChainIntegrity
      <3>3. CASE i = Len(log) + 1
        \* New tail entry: prev_hash = last_hash = log[Len(log)].hash by HashConsistency.
        <4>1. log'[i] = entry
          BY <2>a, <2>c, <3>1, <3>3
        <4>2. entry.prev_hash = last_hash
          OBVIOUS
        <4>3. CASE Len(log) = 0
          \* Then i = 1 and 2..Len(log') = 2..1 = {}, so there is no obligation.
          BY <3>3, <4>3, <3>1
        <4>4. CASE Len(log) > 0
          <5>1. last_hash = log[Len(log)].hash
            BY <2>c, <4>4 DEF HashConsistency
          <5>2. log'[i-1] = log[Len(log)]
            BY <2>a, <2>c, <3>3, <4>4
          <5> QED BY <4>1, <4>2, <5>1, <5>2
        <4> QED BY <4>3, <4>4, <2>c DEF Inv
      <3> QED BY <3>1, <3>2, <3>3
    \* HashConsistency is preserved.
    <2>5. HashConsistency'
      <3>1. Len(log') > 0
        BY <2>a, <2>c
      <3>2. log'[Len(log')] = entry
        BY <2>a, <2>c
      <3>3. last_hash' = entry.hash
        BY <2>a
      <3> QED BY <3>1, <3>2, <3>3 DEF HashConsistency
    \* HashBindsContent is preserved: old records unchanged, new record's hash
    \* is Hash of its own (prev_hash, operation) by construction.
    <2>6. HashBindsContent'
      <3> SUFFICES ASSUME NEW i \in 1..Len(log')
                   PROVE log'[i].hash = Hash(log'[i].prev_hash, log'[i].operation)
        BY DEF HashBindsContent
      <3>1. Len(log') = Len(log) + 1
        BY <2>a, <2>c
      <3>2. CASE i \in 1..Len(log)
        <4>1. log'[i] = log[i]
          BY <2>a, <2>c, <3>2
        <4> QED BY <3>2, <4>1, <2>c DEF HashBindsContent
      <3>3. CASE i = Len(log) + 1
        <4>1. log'[i] = entry
          BY <2>a, <2>c, <3>1, <3>3
        <4>2. entry.hash = Hash(entry.prev_hash, entry.operation)
          OBVIOUS
        <4> QED BY <4>1, <4>2
      <3> QED BY <3>1, <3>2, <3>3
    <2> QED BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF Inv
  <1> QED BY <1>1, <1>2

\* Main safety theorem, parameterized by MaxLogLen.
THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv' BY NextInv
  <1> QED BY <1>1, <1>2, PTL DEF Spec

\* Inv contains both conjuncts of AuditSink!TypeInvariant.
THEOREM TypeSafety == Spec => []TypeInvariant
  <1>1. Inv => TypeInvariant
    BY DEF Inv, TypeInvariant
  <1> QED BY Safety, <1>1, PTL

\* Safety in the carrier's public invariant vocabulary.
THEOREM SafetyOriginal == Spec => [](ChainIntegrity /\ HashConsistency /\ HashBindsContent)
  <1>1. Inv => ChainIntegrity /\ HashConsistency /\ HashBindsContent
    BY DEF Inv
  <1> QED BY Safety, <1>1, PTL

\* Under HashCR, any preimage of a recorded hash has the record's own
\* (prev_hash, operation) pair. The unbounded Nat quantification is not used as
\* a finite TLC invariant.
TamperEvidentInv ==
    \A i \in 1..Len(log) :
        \A p \in Nat, o \in Operations :
            Hash(p, o) = log[i].hash => (p = log[i].prev_hash /\ o = log[i].operation)

THEOREM TamperEvident == Spec => []TamperEvidentInv
  <1>1. Inv => TamperEvidentInv
    <2> SUFFICES ASSUME Inv, NEW i \in 1..Len(log), NEW p \in Nat, NEW o \in Operations,
                        Hash(p, o) = log[i].hash
                 PROVE  p = log[i].prev_hash /\ o = log[i].operation
      BY DEF TamperEvidentInv
    <2>1. log[i] \in LogEntry
      BY DEF Inv
    <2>2. log[i].prev_hash \in Nat /\ log[i].operation \in Operations
      BY <2>1 DEF LogEntry
    <2>3. log[i].hash = Hash(log[i].prev_hash, log[i].operation)
      BY DEF Inv, HashBindsContent
    <2>4. Hash(p, o) = Hash(log[i].prev_hash, log[i].operation)
      BY <2>3
    <2> QED  BY <2>2, <2>4, HashCR
  <1> QED  BY Safety, <1>1, PTL

====
