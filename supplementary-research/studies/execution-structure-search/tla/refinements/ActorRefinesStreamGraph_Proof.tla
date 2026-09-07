---- MODULE ActorRefinesStreamGraph_Proof ----
(* This proof module artifact: TLAPS proof of ActorRefinesStreamGraph.
   Proves TypeInvariant + EdgesTrackRefs + MailboxBounded + NonNegativeRecords +
   StreamGraphRefinement (the conjunction of the previous three, which is
   the actor-to-streaming-graph reduction claim).
   No ASSUME constrains Actors to be finite, so the theorems hold for an
   arbitrary actor set. *)
EXTENDS ActorRefinesStreamGraph, Naturals, Sequences, FiniteSets, TLAPS

ASSUME MaxMailboxType == MaxMailbox \in Nat
ASSUME MaxStepsType == MaxSteps \in Nat

Inv == TypeInvariant /\ EdgesTrackRefs /\ MailboxBounded /\ NonNegativeRecords

LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv  OBVIOUS
  <1>1. TypeInvariant
    BY MaxStepsType DEF Init, TypeInvariant
  <1>2. EdgesTrackRefs
    BY DEF Init, EdgesTrackRefs
  <1>3. MailboxBounded
    BY MaxMailboxType DEF Init, MailboxBounded
  <1>4. NonNegativeRecords
    BY DEF Init, NonNegativeRecords
  <1> QED  BY <1>1, <1>2, <1>3, <1>4 DEF Inv

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'  OBVIOUS
  <1> USE DEF Inv, TypeInvariant, EdgesTrackRefs, MailboxBounded, NonNegativeRecords
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF vars
  <1>A. CASE \E a, b \in Actors : Introduce(a, b)
    <2> SUFFICES ASSUME NEW a \in Actors, NEW b \in Actors, Introduce(a, b)
                 PROVE Inv'
      BY <1>A
    <2>a. a # b                                          BY DEF Introduce
    <2>b. b \notin refs[a]                               BY DEF Introduce
    <2>c. steps < MaxSteps                               BY DEF Introduce
    <2>d. refs' = [refs EXCEPT ![a] = refs[a] \cup {b}]  BY DEF Introduce
    <2>e. sg_edges' = sg_edges \cup {<<a, b>>}           BY DEF Introduce
    <2>f. steps' = steps + 1                             BY DEF Introduce
    <2>g. UNCHANGED <<mailbox, behavior, sg_records>>    BY DEF Introduce
    <2>1. TypeInvariant'
      <3>1. mailbox' \in [Actors -> Seq(Messages)]       BY <2>g
      <3>2. refs' \in [Actors -> SUBSET Actors]
        BY <2>d
      <3>3. behavior' \in [Actors -> {"active", "swapped"}]    BY <2>g
      <3>4. sg_edges' \subseteq Actors \X Actors
        BY <2>e
      <3>5. sg_records' \in [Actors \X Actors -> Nat]    BY <2>g
      <3>6. steps' \in 0..MaxSteps
        BY <2>c, <2>f, MaxStepsType
      <3> QED  BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6
    <2>2. EdgesTrackRefs'
      \* sg_edges' adds <<a,b>>; refs'[a] adds b; other refs[c] unchanged.
      <3>1. sg_edges' = {p \in Actors \X Actors : p[2] \in refs'[p[1]]}
        BY <2>a, <2>b, <2>d, <2>e DEF EdgesTrackRefs
      <3> QED  BY <3>1 DEF EdgesTrackRefs
    <2>3. MailboxBounded'                                BY <2>g
    <2>4. NonNegativeRecords'                            BY <2>g
    <2> QED  BY <2>1, <2>2, <2>3, <2>4
  <1>B. CASE \E s, t \in Actors, m \in Messages : Send(s, t, m)
    <2> SUFFICES ASSUME NEW s \in Actors, NEW t \in Actors, NEW m \in Messages,
                         Send(s, t, m)
                 PROVE Inv'
      BY <1>B
    <2>a. t \in refs[s]                                  BY DEF Send
    <2>b. Len(mailbox[t]) < MaxMailbox                   BY DEF Send
    <2>c. steps < MaxSteps                               BY DEF Send
    <2>d. mailbox' = [mailbox EXCEPT ![t] = Append(mailbox[t], m)]   BY DEF Send
    <2>e. sg_records' = [sg_records EXCEPT ![<<s, t>>] = sg_records[<<s, t>>] + 1]
      BY DEF Send
    <2>f. steps' = steps + 1                             BY DEF Send
    <2>g. UNCHANGED <<refs, behavior, sg_edges>>         BY DEF Send
    <2>1. TypeInvariant'
      <3>1. mailbox' \in [Actors -> Seq(Messages)]
        BY <2>d
      <3>2. refs' \in [Actors -> SUBSET Actors]          BY <2>g
      <3>3. behavior' \in [Actors -> {"active", "swapped"}]    BY <2>g
      <3>4. sg_edges' \subseteq Actors \X Actors         BY <2>g
      <3>5. sg_records' \in [Actors \X Actors -> Nat]
        BY <2>e
      <3>6. steps' \in 0..MaxSteps
        BY <2>c, <2>f, MaxStepsType
      <3> QED  BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6
    <2>2. EdgesTrackRefs'                                BY <2>g
    <2>3. MailboxBounded'
      <3> SUFFICES ASSUME NEW c \in Actors PROVE Len(mailbox'[c]) <= MaxMailbox
        BY DEF MailboxBounded
      <3>A. CASE c = t
        <4>1. mailbox'[c] = Append(mailbox[t], m)        BY <2>d, <3>A
        <4>2. Len(Append(mailbox[t], m)) = Len(mailbox[t]) + 1   OBVIOUS
        <4>3. Len(mailbox[t]) < MaxMailbox               BY <2>b
        <4> QED  BY <4>1, <4>2, <4>3, MaxMailboxType
      <3>B. CASE c # t
        <4>1. mailbox'[c] = mailbox[c]                   BY <2>d, <3>B
        <4> QED  BY <4>1 DEF MailboxBounded
      <3> QED  BY <3>A, <3>B
    <2>4. NonNegativeRecords'
      <3> SUFFICES ASSUME NEW p \in Actors \X Actors PROVE sg_records'[p] >= 0
        BY DEF NonNegativeRecords
      <3>A. CASE p = <<s, t>>
        <4>1. sg_records'[p] = sg_records[<<s, t>>] + 1  BY <2>e, <3>A
        <4> QED  BY <4>1 DEF NonNegativeRecords
      <3>B. CASE p # <<s, t>>
        <4>1. sg_records'[p] = sg_records[p]             BY <2>e, <3>B
        <4> QED  BY <4>1 DEF NonNegativeRecords
      <3> QED  BY <3>A, <3>B
    <2> QED  BY <2>1, <2>2, <2>3, <2>4
  <1>C. CASE \E a \in Actors : Receive(a)
    <2> SUFFICES ASSUME NEW a \in Actors, Receive(a) PROVE Inv'
      BY <1>C
    <2>a. Len(mailbox[a]) > 0                            BY DEF Receive
    <2>b. mailbox' = [mailbox EXCEPT ![a] = Tail(mailbox[a])]   BY DEF Receive
    <2>c. \E sender \in Actors :
            /\ sg_records[<<sender, a>>] > 0
            /\ sg_records' = [sg_records EXCEPT ![<<sender, a>>] = sg_records[<<sender, a>>] - 1]
      BY DEF Receive
    <2>d. steps' = steps + 1                             BY DEF Receive
    <2>e. UNCHANGED <<refs, behavior, sg_edges>>         BY DEF Receive
    <2>f. steps < MaxSteps                               BY DEF Receive
    <2> SUFFICES ASSUME NEW sender \in Actors,
                         sg_records[<<sender, a>>] > 0,
                         sg_records' = [sg_records EXCEPT ![<<sender, a>>] = sg_records[<<sender, a>>] - 1]
                 PROVE Inv'
      BY <2>c
    <2>1. TypeInvariant'
      <3>0. mailbox \in [Actors -> Seq(Messages)]
        BY DEF TypeInvariant
      <3>1. mailbox' \in [Actors -> Seq(Messages)]
        BY <2>a, <2>b, <3>0
      <3>2. refs' \in [Actors -> SUBSET Actors]          BY <2>e DEF TypeInvariant
      <3>3. behavior' \in [Actors -> {"active", "swapped"}]    BY <2>e DEF TypeInvariant
      <3>4. sg_edges' \subseteq Actors \X Actors         BY <2>e DEF TypeInvariant
      <3>5. sg_records' \in [Actors \X Actors -> Nat]
        BY DEF TypeInvariant, NonNegativeRecords
      <3>6. steps' \in 0..MaxSteps
        BY <2>d, <2>f, MaxStepsType
      <3> QED  BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6
    <2>2. EdgesTrackRefs'                                BY <2>e
    <2>3. MailboxBounded'
      <3> SUFFICES ASSUME NEW c \in Actors PROVE Len(mailbox'[c]) <= MaxMailbox
        BY DEF MailboxBounded
      <3>A. CASE c = a
        <4>1. mailbox'[c] = Tail(mailbox[a])             BY <2>b, <3>A
        <4>2. Len(Tail(mailbox[a])) = Len(mailbox[a]) - 1   BY <2>a
        <4>3. Len(mailbox[a]) <= MaxMailbox              OBVIOUS
        <4> QED  BY <4>1, <4>2, <4>3, MaxMailboxType
      <3>B. CASE c # a
        <4>1. mailbox'[c] = mailbox[c]                   BY <2>b, <3>B
        <4> QED  BY <4>1
      <3> QED  BY <3>A, <3>B
    <2>4. NonNegativeRecords'
      <3> SUFFICES ASSUME NEW p \in Actors \X Actors PROVE sg_records'[p] >= 0
        BY DEF NonNegativeRecords
      <3>A. CASE p = <<sender, a>>
        <4>0. sg_records' = [sg_records EXCEPT ![<<sender, a>>] = sg_records[<<sender, a>>] - 1]
          OBVIOUS
        <4>1. sg_records'[p] = sg_records[<<sender, a>>] - 1
          BY <3>A, <4>0
        <4>2. sg_records[<<sender, a>>] > 0
          OBVIOUS
        <4> QED  BY <4>1, <4>2
      <3>B. CASE p # <<sender, a>>
        <4>1. sg_records' = [sg_records EXCEPT ![<<sender, a>>] = sg_records[<<sender, a>>] - 1]
          OBVIOUS
        <4>2. sg_records'[p] = sg_records[p]
          BY <3>B, <4>1
        <4> QED  BY <4>2 DEF NonNegativeRecords
      <3> QED  BY <3>A, <3>B
    <2> QED  BY <2>1, <2>2, <2>3, <2>4
  <1>D. CASE \E a \in Actors : Become(a)
    <2> SUFFICES ASSUME NEW a \in Actors, Become(a) PROVE Inv'
      BY <1>D
    <2>a. steps < MaxSteps                               BY DEF Become
    <2>b. behavior' = [behavior EXCEPT ![a] =
                          IF behavior[a] = "active" THEN "swapped" ELSE "active"]
      BY DEF Become
    <2>c. steps' = steps + 1                             BY DEF Become
    <2>d. UNCHANGED <<mailbox, refs, sg_edges, sg_records>>   BY DEF Become
    <2>1. TypeInvariant'
      <3>1. mailbox' \in [Actors -> Seq(Messages)]       BY <2>d
      <3>2. refs' \in [Actors -> SUBSET Actors]          BY <2>d
      <3>3. behavior' \in [Actors -> {"active", "swapped"}]
        BY <2>b
      <3>4. sg_edges' \subseteq Actors \X Actors         BY <2>d
      <3>5. sg_records' \in [Actors \X Actors -> Nat]    BY <2>d
      <3>6. steps' \in 0..MaxSteps
        BY <2>a, <2>c, MaxStepsType
      <3> QED  BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6
    <2>2. EdgesTrackRefs'                                BY <2>d
    <2>3. MailboxBounded'                                BY <2>d
    <2>4. NonNegativeRecords'                            BY <2>d
    <2> QED  BY <2>1, <2>2, <2>3, <2>4
  <1>E. CASE Done
    BY <1>E DEF Done, vars
  <1>X. CASE Next
    BY <1>X, <1>A, <1>B, <1>C, <1>D, <1>E DEF Next
  <1> QED  BY <1>0, <1>X

THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv               BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'  BY NextInv
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

THEOREM TypeSafety == Spec => []TypeInvariant       BY Safety, PTL DEF Inv
THEOREM EdgesTrackRefsSafety == Spec => []EdgesTrackRefs  BY Safety, PTL DEF Inv
THEOREM MailboxBoundedSafety == Spec => []MailboxBounded  BY Safety, PTL DEF Inv
THEOREM NonNegativeRecordsSafety == Spec => []NonNegativeRecords  BY Safety, PTL DEF Inv
THEOREM StreamGraphRefinementSafety == Spec => []StreamGraphRefinement
  <1>1. Inv => StreamGraphRefinement
    BY DEF Inv, StreamGraphRefinement
  <1> QED  BY Safety, <1>1, PTL
====
