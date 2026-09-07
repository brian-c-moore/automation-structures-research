---- MODULE SignalFromAuditSink_Proof ----
(***************************************************************************
  TLAPS proof of the AuditSink-plus-cursor refinement to Signal.

  Discharges, unbounded and parametric:

      Refinement == Spec => Sig!Spec

  Every behaviour of the AuditSink log plus pull cursors is a Signal behavior.

  Log updates unfold through ASink.Record. HashTypeAss is the Nat-closure
  premise needed by the AuditSink record shape, and the inductive invariant
  preserves ChainIntegrity, HashConsistency, and HashBindsContent.

  The proof also establishes the four configured invariants (TypeInvariant,
  ChainIntegrity, HashConsistency, HashBindsContent) as corollaries of
  []Inv, with the inductive strengthening log \in Seq(LogEntry) -- the
  AuditSink_Proof.tla idiom: the record shape is needed for the
  .prev_hash/.hash/.operation field accesses, and HashConsistency witnesses
  ChainIntegrity across an append.

  No concrete constants are assumed. Values and Listeners are
  arbitrary sets (no cardinality is used anywhere; Listeners may be empty),
  MaxLogLen is any natural, Hash is any Nat-closed function of (prev, op),
  InitialValue \in Values is the base module's own ASSUME restated under a
  name so BY clauses can cite it. HashC is not unfolded; the result holds for
  every Hash satisfying HashTypeAss.
 ***************************************************************************)
EXTENDS SignalFromAuditSink, TLAPS

ASSUME MaxLogLenAss == MaxLogLen \in Nat

\* Names the base module's unnamed `ASSUME InitialValue \in Values` so proof
\* steps can cite it.
ASSUME InitialValueAss == InitialValue \in Values

\* The abstract Hash parameter is Nat-closed -- AuditSink_Proof's own
\* HashType assumption, instantiated at Operations <- Values.
ASSUME HashTypeAss == \A p \in Nat, v \in Values : Hash(p, v) \in Nat

\* Shape of a log entry; matches the record built in ASink!Record(v).
LogEntry == [operation : Values, prev_hash : Nat, hash : Nat]

\* Inductive strengthening: Seq typing + the construction's four checked
\* invariants (TypeInvariant carries the cursor bounds the refinement needs;
\* HashConsistency witnesses ChainIntegrity across an append).
Inv ==
    /\ log \in Seq(LogEntry)
    /\ TypeInvariant
    /\ ChainIntegrity
    /\ HashConsistency
    /\ HashBindsContent

(*-------------------------------------------------------------------------*)
(* Lemma: Init establishes the inductive invariant.                        *)
(*-------------------------------------------------------------------------*)
LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv
    OBVIOUS
  <1>a. log = <<>> /\ last_hash = 0 /\ cursor = [l \in Listeners |-> 0]
    BY DEF Init, ASink!Init
  <1>1. log \in Seq(LogEntry)
    BY <1>a
  <1>2. TypeInvariant
    <2>1. last_hash \in Nat
      BY <1>a
    <2>2. Len(log) <= MaxLogLen
      BY <1>a, MaxLogLenAss
    <2>3. cursor \in [Listeners -> 0..MaxLogLen]
      BY <1>a, MaxLogLenAss
    <2>4. \A m \in Listeners : cursor[m] <= Len(log)
      BY <1>a
    <2> QED BY <2>1, <2>2, <2>3, <2>4
      DEF TypeInvariant, ASink!TypeInvariant
  <1>3. ChainIntegrity
    \* log = <<>>, so 2..Len(log) = {}; the universal is vacuous.
    BY <1>a DEF ChainIntegrity, ASink!ChainIntegrity
  <1>4. HashConsistency
    BY <1>a DEF HashConsistency, ASink!HashConsistency
  <1>5. HashBindsContent
    BY <1>a DEF HashBindsContent, ASink!HashBindsContent
  <1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF Inv

(*-------------------------------------------------------------------------*)
(* Lemma: every Next step preserves the inductive invariant.               *)
(*-------------------------------------------------------------------------*)
LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <1>c. /\ log \in Seq(LogEntry)
        /\ last_hash \in Nat
        /\ Len(log) <= MaxLogLen
        /\ cursor \in [Listeners -> 0..MaxLogLen]
        /\ \A m \in Listeners : cursor[m] <= Len(log)
        /\ ChainIntegrity
        /\ HashConsistency
        /\ HashBindsContent
    BY DEF Inv, TypeInvariant, ASink!TypeInvariant
  <1>len. Len(log) \in Nat
    BY <1>c
  <1>0. CASE UNCHANGED vars
    BY <1>0, <1>c
       DEF Inv, vars, TypeInvariant, ASink!TypeInvariant,
           ChainIntegrity, ASink!ChainIntegrity,
           HashConsistency, ASink!HashConsistency,
           HashBindsContent, ASink!HashBindsContent
  <1>1. CASE Next
    <2>A. CASE \E v \in Values : SetValue(v)
      <3> SUFFICES ASSUME NEW v \in Values, SetValue(v) PROVE Inv'
        BY <2>A
      <3> DEFINE nh    == Hash(last_hash, v)
      <3> DEFINE entry == [operation |-> v, prev_hash |-> last_hash,
                           hash |-> nh]
      <3>a. /\ v /= CurrentValue
            /\ Len(log) < MaxLogLen
            /\ log' = Append(log, entry)
            /\ last_hash' = nh
            /\ cursor' = cursor
        BY DEF SetValue, ASink!Record
      <3>d. nh \in Nat
        BY <1>c, HashTypeAss
      <3>e. entry \in LogEntry
        BY <1>c, <3>d DEF LogEntry
      <3>len. Len(log') = Len(log) + 1
        BY <3>a, <3>e, <1>c
      <3>1. log' \in Seq(LogEntry)
        BY <3>a, <3>e, <1>c
      <3>2. TypeInvariant'
        <4>1. last_hash' \in Nat
          BY <3>a, <3>d
        <4>2. Len(log') <= MaxLogLen
          BY <3>a, <3>len, <1>len, <1>c, MaxLogLenAss
        <4>3. cursor' \in [Listeners -> 0..MaxLogLen]
          BY <3>a, <1>c
        <4>4. \A m \in Listeners : cursor'[m] <= Len(log')
          BY <3>a, <3>len, <1>c, <1>len
        <4> QED BY <4>1, <4>2, <4>3, <4>4
          DEF TypeInvariant, ASink!TypeInvariant
      <3>3. ChainIntegrity'
        <4> SUFFICES ASSUME NEW i \in 2..Len(log')
                     PROVE log'[i].prev_hash = log'[i-1].hash
          BY DEF ChainIntegrity, ASink!ChainIntegrity
        <4>1. CASE i \in 2..Len(log)
          <5>1. log'[i] = log[i] /\ log'[i-1] = log[i-1]
            BY <3>a, <3>e, <1>c, <4>1
          <5> QED BY <4>1, <5>1, <1>c
            DEF ChainIntegrity, ASink!ChainIntegrity
        <4>2. CASE i = Len(log) + 1
          <5>1. log'[i] = entry
            BY <3>a, <3>e, <1>c, <3>len, <4>2
          <5>2. entry.prev_hash = last_hash
            OBVIOUS
          <5>3. CASE Len(log) = 0
            \* Then i = 1, contradicting i \in 2..Len(log') with Len(log')=1.
            BY <4>2, <5>3, <3>len
          <5>4. CASE Len(log) > 0
            <6>1. last_hash = log[Len(log)].hash
              BY <1>c, <5>4 DEF HashConsistency, ASink!HashConsistency
            <6>2. log'[i-1] = log[Len(log)]
              BY <3>a, <3>e, <1>c, <4>2, <5>4
            <6> QED BY <5>1, <5>2, <6>1, <6>2
          <5> QED BY <5>3, <5>4, <1>len
        <4> QED BY <4>1, <4>2, <3>len, <1>len
      <3>4. HashConsistency'
        <4>1. Len(log') > 0
          BY <3>len, <1>len
        <4>2. log'[Len(log')] = entry
          BY <3>a, <3>e, <1>c
        <4>3. last_hash' = entry.hash
          BY <3>a
        <4> QED BY <4>1, <4>2, <4>3
          DEF HashConsistency, ASink!HashConsistency
      <3>5. HashBindsContent'
        <4> SUFFICES ASSUME NEW i \in 1..Len(log')
                     PROVE log'[i].hash = Hash(log'[i].prev_hash,
                                               log'[i].operation)
          BY DEF HashBindsContent, ASink!HashBindsContent
        <4>1. CASE i \in 1..Len(log)
          <5>1. log'[i] = log[i]
            BY <3>a, <3>e, <1>c, <4>1
          <5> QED BY <4>1, <5>1, <1>c
            DEF HashBindsContent, ASink!HashBindsContent
        <4>2. CASE i = Len(log) + 1
          <5>1. log'[i] = entry
            BY <3>a, <3>e, <1>c, <3>len, <4>2
          <5>2. entry.hash = Hash(entry.prev_hash, entry.operation)
            OBVIOUS
          <5> QED BY <5>1, <5>2
        <4> QED BY <4>1, <4>2, <3>len, <1>len
      <3> QED BY <3>1, <3>2, <3>3, <3>4, <3>5 DEF Inv
    <2>B. CASE \E l \in Listeners : NotifyListener(l)
      <3> SUFFICES ASSUME NEW l \in Listeners, NotifyListener(l) PROVE Inv'
        BY <2>B
      <3>a. /\ cursor[l] < Len(log)
            /\ cursor' = [cursor EXCEPT ![l] = Len(log)]
            /\ log' = log
            /\ last_hash' = last_hash
        BY DEF NotifyListener
      <3>1. log' \in Seq(LogEntry)
        BY <3>a, <1>c
      <3>2. TypeInvariant'
        <4>1. last_hash' \in Nat
          BY <3>a, <1>c
        <4>2. Len(log') <= MaxLogLen
          BY <3>a, <1>c
        <4>3. cursor' \in [Listeners -> 0..MaxLogLen]
          BY <3>a, <1>c, <1>len
        <4>4. \A m \in Listeners : cursor'[m] <= Len(log')
          BY <3>a, <1>c, <1>len
        <4> QED BY <4>1, <4>2, <4>3, <4>4
          DEF TypeInvariant, ASink!TypeInvariant
      <3>3. ChainIntegrity'
        BY <3>a, <1>c DEF ChainIntegrity, ASink!ChainIntegrity
      <3>4. HashConsistency'
        BY <3>a, <1>c DEF HashConsistency, ASink!HashConsistency
      <3>5. HashBindsContent'
        BY <3>a, <1>c DEF HashBindsContent, ASink!HashBindsContent
      <3> QED BY <3>1, <3>2, <3>3, <3>4, <3>5 DEF Inv
    <2> QED BY <2>A, <2>B, <1>1 DEF Next
  <1> QED BY <1>0, <1>1

(*-------------------------------------------------------------------------*)
(* Safety: the inductive invariant holds in every reachable state.         *)
(*-------------------------------------------------------------------------*)
THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv
    BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'
    BY NextInv
  <1> QED BY <1>1, <1>2, PTL DEF Spec

\* Parametric forms of the four configured invariants.
THEOREM TypeSafety == Spec => []TypeInvariant
  BY Safety, PTL DEF Inv

THEOREM ChainSafety ==
    Spec => [](ChainIntegrity /\ HashConsistency /\ HashBindsContent)
  BY Safety, PTL DEF Inv

(*-------------------------------------------------------------------------*)
(* The refinement: Init maps to Sig!Init, every step maps to a Sig step    *)
(* or a Sig stutter.                                                       *)
(*-------------------------------------------------------------------------*)
LEMMA InitRefines == Init => Sig!Init
  <1> SUFFICES ASSUME Init PROVE Sig!Init
    OBVIOUS
  <1>a. log = <<>> /\ cursor = [l \in Listeners |-> 0]
    BY DEF Init, ASink!Init
  <1>1. CurrentValue = InitialValue
    BY <1>a DEF CurrentValue
  <1>2. CurrentValue \in Values
    BY <1>1, InitialValueAss
  <1>3. Len(log) = 0
    BY <1>a
  <1>4. MapPending = {}
    BY <1>a DEF MapPending
  <1>5. MapNotified = {}
    BY <1>a DEF MapNotified
  <1> QED BY <1>2, <1>3, <1>4, <1>5 DEF Sig!Init

LEMMA NextRefines == Inv /\ [Next]_vars => [Sig!Next]_(Sig!vars)
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE [Sig!Next]_(Sig!vars)
    OBVIOUS
  <1>c. /\ log \in Seq(LogEntry)
        /\ last_hash \in Nat
        /\ Len(log) <= MaxLogLen
        /\ cursor \in [Listeners -> 0..MaxLogLen]
        /\ \A m \in Listeners : cursor[m] <= Len(log)
    BY DEF Inv, TypeInvariant, ASink!TypeInvariant
  <1>len. Len(log) \in Nat
    BY <1>c
  <1>0. CASE UNCHANGED vars
    <2>1. UNCHANGED <<CurrentValue, Len(log) > 0, MapPending, MapNotified>>
      BY <1>0 DEF vars, CurrentValue, MapPending, MapNotified
    <2> QED BY <2>1 DEF Sig!vars
  <1>1. CASE Next
    <2>A. CASE \E v \in Values : SetValue(v)
      <3> SUFFICES ASSUME NEW v \in Values, SetValue(v)
                   PROVE  [Sig!Next]_(Sig!vars)
        BY <2>A
      <3> DEFINE nh    == Hash(last_hash, v)
      <3> DEFINE entry == [operation |-> v, prev_hash |-> last_hash,
                           hash |-> nh]
      <3>a. /\ v /= CurrentValue
            /\ Len(log) < MaxLogLen
            /\ log' = Append(log, entry)
            /\ last_hash' = nh
            /\ cursor' = cursor
        BY DEF SetValue, ASink!Record
      <3>d. nh \in Nat
        BY <1>c, HashTypeAss
      <3>e. entry \in LogEntry
        BY <1>c, <3>d DEF LogEntry
      <3>len. Len(log') = Len(log) + 1
        BY <3>a, <3>e, <1>c
      <3>1. CurrentValue' = v
        <4>1. Len(log') > 0
          BY <3>len, <1>len
        <4>2. log'[Len(log')] = entry
          BY <3>a, <3>e, <1>c
        <4>3. entry.operation = v
          OBVIOUS
        <4> QED BY <4>1, <4>2, <4>3 DEF CurrentValue
      <3>2. MapPending' = Listeners
        <4>1. \A m \in Listeners : cursor'[m] < Len(log')
          BY <3>a, <3>len, <1>c, <1>len
        <4> QED BY <4>1 DEF MapPending
      <3>3. MapNotified' = {}
        <4>1. \A m \in Listeners : ~(cursor'[m] = Len(log'))
          BY <3>a, <3>len, <1>c, <1>len
        <4> QED BY <4>1 DEF MapNotified
      <3>4. Sig!SetValue(v)
        BY <3>a, <3>len, <3>1, <3>2, <3>3, <1>len DEF Sig!SetValue
      <3> QED BY <3>4 DEF Sig!Next
    <2>B. CASE \E l \in Listeners : NotifyListener(l)
      <3> SUFFICES ASSUME NEW l \in Listeners, NotifyListener(l)
                   PROVE  [Sig!Next]_(Sig!vars)
        BY <2>B
      <3>a. /\ cursor[l] < Len(log)
            /\ cursor' = [cursor EXCEPT ![l] = Len(log)]
            /\ log' = log
            /\ last_hash' = last_hash
        BY DEF NotifyListener
      <3>b. \A m \in Listeners :
                cursor'[m] = IF m = l THEN Len(log) ELSE cursor[m]
        BY <3>a, <1>c
      <3>pos. Len(log) > 0
        \* cursor[l] \in 0..MaxLogLen so cursor[l] >= 0; cursor[l] < Len(log).
        BY <3>a, <1>c, <1>len
      <3>1. l \in MapPending
        BY <3>a DEF MapPending
      <3>2. MapPending' = MapPending \ {l}
        BY <3>a, <3>b, <1>len DEF MapPending
      <3>3. MapNotified' = MapNotified \cup {l}
        BY <3>a, <3>b, <3>pos, <1>len DEF MapNotified
      <3>4. CurrentValue' = CurrentValue
        BY <3>a DEF CurrentValue
      <3>5. Sig!NotifyListener(l)
        BY <3>a, <3>1, <3>2, <3>3, <3>4 DEF Sig!NotifyListener
      <3> QED BY <3>5 DEF Sig!Next
    <2> QED BY <2>A, <2>B, <1>1 DEF Next
  <1> QED BY <1>0, <1>1

(*-------------------------------------------------------------------------*)
(* The construction refines Signal parametrically.                         *)
(*-------------------------------------------------------------------------*)
THEOREM Refinement == Spec => Sig!Spec
  <1>1. Init => Sig!Init
    BY InitRefines
  <1>2. Inv /\ [Next]_vars => [Sig!Next]_(Sig!vars)
    BY NextRefines
  <1>3. Spec => []Inv
    BY Safety
  <1> QED BY <1>1, <1>2, <1>3, PTL DEF Spec, Sig!Spec

\* Restatement in the base module's own vocabulary.
THEOREM RefinementOriginal == Spec => SigRefinement
  BY Refinement DEF SigRefinement
====
