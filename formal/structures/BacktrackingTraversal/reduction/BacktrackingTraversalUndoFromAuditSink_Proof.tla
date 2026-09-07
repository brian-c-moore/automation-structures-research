---- MODULE BacktrackingTraversalUndoFromAuditSink_Proof ----
(***************************************************************************
  Parametric TLAPS proof for the AuditSink construction of
  BacktrackingTraversalUndo.

  It establishes TypeSafety, ComponentSafetySafety, MappedPairingSafety,
  MappedStateRestorationSafety, and Refinement. The target ledger and auxiliary
  state are projections of AuditSink records and carry rather than renamed
  variables.

  AuditSink's chain obligations supply StateRestoration and the value half of
  Pairing. The count relation Len(ledger) = Depth is a separate invariant over
  cursor glue. The first-token anchor follows from AuditSink initialization and
  requires InitAux = 0. MaxDepth typing and Mutate closure are the remaining
  component premises.

  No target Ascend step is proved because the construction has no action that
  shrinks the AuditSink log. Refinement therefore holds for a strict behavior
  subset and does not satisfy the full-action-surface reduction criterion.
 ***************************************************************************)
EXTENDS BacktrackingTraversalUndoFromAuditSink, Naturals, Sequences,
        SequenceTheorems, TLAPS

\* The component's own two constant assumptions, read through the
\* substitution MaxLogLen <- MaxDepth, Hash <- Mutate, Operations <- Deltas.
ASSUME MaxDepthType == MaxDepth \in Nat
ASSUME MutateNat    == \A p \in Nat, d \in Deltas : Mutate(p, d) \in Nat

\* AuditSink Init fixes last_hash at zero, so the empty-ledger mapping requires
\* InitAux = 0.
ASSUME InitAuxZero  == InitAux = 0

\* Shapes. LogEntry is the component's record; LedgerEntry is what the
\* CF-001 projection makes of it.
LogEntry    == [operation : Deltas, prev_hash : Nat, hash : Nat]
LedgerEntry == [saved : Nat, delta : Deltas]

\* The first-link anchor follows from AuditSink initialization and supplies
\* the first clause of StateRestoration.
FirstLink == Len(log) >= 1 => log[1].prev_hash = 0

Inv ==
  /\ log \in Seq(LogEntry)
  /\ last_hash \in Nat
  /\ Len(log) <= MaxDepth
  /\ c_path \in Seq(1..BranchFactor)
  /\ c_visited \subseteq Seq(1..BranchFactor)
  /\ Len(c_path) = Len(log)
  /\ ComponentSafety
  /\ FirstLink

(*-------------------------------------------------------------------------*)
(* The projection lemma. Everything the mapped obligations and the          *)
(* refinement need to know about LedgerView is here, proved once.          *)
(*-------------------------------------------------------------------------*)
LEMMA LedgerViewProps ==
  ASSUME log \in Seq(LogEntry)
  PROVE  /\ LedgerView \in Seq(LedgerEntry)
         /\ Len(LedgerView) = Len(log)
         /\ \A i \in 1..Len(log) :
                LedgerView[i] = [saved |-> log[i].prev_hash,
                                 delta |-> log[i].operation]
  <1>1. Len(log) \in Nat /\ log \in [1..Len(log) -> LogEntry]
    BY LenProperties
  <1>2. LedgerView \in [1..Len(log) -> LedgerEntry]
    BY <1>1 DEF LedgerView, LogEntry, LedgerEntry
  <1>3. LedgerView \in Seq(LedgerEntry)
    BY <1>1, <1>2
  <1>4. DOMAIN LedgerView = 1..Len(log)
    BY <1>2
  <1>5. Len(LedgerView) \in Nat /\ DOMAIN LedgerView = 1..Len(LedgerView)
    BY <1>3, LenProperties
  <1>6. Len(LedgerView) = Len(log)
    BY <1>1, <1>4, <1>5
  <1>7. \A i \in 1..Len(log) :
            LedgerView[i] = [saved |-> log[i].prev_hash,
                             delta |-> log[i].operation]
    BY <1>1 DEF LedgerView
  <1> QED  BY <1>3, <1>6, <1>7

(*-------------------------------------------------------------------------*)
(* The inductive invariant.                                                *)
(*-------------------------------------------------------------------------*)
LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv  OBVIOUS
  <1>i. log = <<>> /\ last_hash = 0
    BY DEF Init, ASink!Init
  <1>p. c_path = <<>> /\ c_visited = {}
    BY DEF Init
  <1>l. Len(log) = 0 /\ Len(c_path) = 0
    BY <1>i, <1>p, EmptySeq
  <1>1. log \in Seq(LogEntry)
    BY <1>i, EmptySeq
  <1>2. last_hash \in Nat
    BY <1>i
  <1>3. Len(log) <= MaxDepth
    BY <1>l, MaxDepthType
  <1>4. c_path \in Seq(1..BranchFactor)
    BY <1>p, EmptySeq
  <1>5. c_visited \subseteq Seq(1..BranchFactor)
    BY <1>p
  <1>6. Len(c_path) = Len(log)
    BY <1>l
  <1>7. ComponentSafety
    BY <1>i, <1>l
    DEF ComponentSafety, ASink!ChainIntegrity, ASink!HashConsistency,
        ASink!HashBindsContent
  <1>8. FirstLink
    BY <1>l DEF FirstLink
  <1> QED  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8 DEF Inv

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'  OBVIOUS
  <1>nat. /\ log \in Seq(LogEntry)
          /\ last_hash \in Nat
          /\ Len(log) <= MaxDepth
          /\ c_path \in Seq(1..BranchFactor)
          /\ c_visited \subseteq Seq(1..BranchFactor)
          /\ Len(c_path) = Len(log)
          /\ ComponentSafety
          /\ FirstLink
          /\ Len(log) \in Nat
          /\ Len(c_path) \in Nat
    BY LenProperties DEF Inv
  <1>0. CASE UNCHANGED vars
    BY <1>0, <1>nat
    DEF Inv, vars, ComponentSafety, FirstLink,
        ASink!ChainIntegrity, ASink!HashConsistency, ASink!HashBindsContent
  (* ---- CDescend(c, d) -------------------------------------------------- *)
  <1>1. CASE \E c \in 1..BranchFactor, d \in Deltas : CDescend(c, d)
    <2> SUFFICES ASSUME NEW c \in 1..BranchFactor, NEW d \in Deltas, CDescend(c, d)
                 PROVE  Inv'
      BY <1>1
    <2> DEFINE entry == [operation |-> d,
                         prev_hash |-> last_hash,
                         hash      |-> Mutate(last_hash, d)]
    <2>a. log' = Append(log, entry) /\ last_hash' = Mutate(last_hash, d)
      BY DEF CDescend, ASink!Record
    <2>b. Len(log) < MaxDepth
      BY DEF CDescend, ASink!Record
    <2>p. c_path' = Append(c_path, c) /\ c_visited' = c_visited
      BY DEF CDescend
    <2>h. Mutate(last_hash, d) \in Nat
      BY <1>nat, MutateNat
    <2>e. entry \in LogEntry
      BY <1>nat, <2>h DEF LogEntry
    <2>ap. /\ log' \in Seq(LogEntry)
           /\ Len(log') = Len(log) + 1
           /\ \A i \in 1..Len(log) : log'[i] = log[i]
           /\ log'[Len(log) + 1] = entry
      BY <2>a, <2>e, <1>nat, AppendProperties
    <2>cp. /\ c_path' \in Seq(1..BranchFactor)
           /\ Len(c_path') = Len(c_path) + 1
      BY <2>p, <1>nat, AppendProperties
    <2>1. log' \in Seq(LogEntry)
      BY <2>ap
    <2>2. last_hash' \in Nat
      BY <2>a, <2>h
    <2>3. Len(log') <= MaxDepth
      BY <2>ap, <2>b, <1>nat, MaxDepthType
    <2>4. c_path' \in Seq(1..BranchFactor)
      BY <2>cp
    <2>5. c_visited' \subseteq Seq(1..BranchFactor)
      BY <2>p, <1>nat
    <2>6. Len(c_path') = Len(log')
      BY <2>ap, <2>cp, <1>nat
    <2>7. ComponentSafety'
      <3>ci. ASink!ChainIntegrity'
        <4> SUFFICES ASSUME NEW i \in 2..Len(log')
                     PROVE  log'[i].prev_hash = log'[i-1].hash
          BY DEF ASink!ChainIntegrity
        <4>1. CASE i \in 2..Len(log)
          <5>1. i - 1 \in 1..Len(log)                    BY <4>1, <1>nat
          <5>2. log'[i] = log[i]                         BY <4>1, <2>ap
          <5>3. log'[i-1] = log[i-1]                     BY <5>1, <2>ap
          <5> QED  BY <5>2, <5>3, <4>1, <1>nat
                   DEF ComponentSafety, ASink!ChainIntegrity
        <4>2. CASE i = Len(log) + 1
          <5>1. log'[i] = entry
            BY <4>2, <2>ap
          <5>2. Len(log) >= 1
            BY <4>2, <1>nat
          <5>3. log'[i-1] = log[Len(log)]
            BY <4>2, <5>2, <2>ap, <1>nat
          <5>4. last_hash = log[Len(log)].hash
            BY <5>2, <1>nat
            DEF ComponentSafety, ASink!HashConsistency
          <5> QED  BY <5>1, <5>3, <5>4
        <4> QED  BY <4>1, <4>2, <2>ap, <1>nat
      <3>hc. ASink!HashConsistency'
        <4>1. Len(log') > 0
          BY <2>ap, <1>nat
        <4>2. log'[Len(log')] = entry
          BY <2>ap, <1>nat
        <4> QED  BY <4>1, <4>2, <2>a DEF ASink!HashConsistency
      <3>hb. ASink!HashBindsContent'
        <4> SUFFICES ASSUME NEW i \in 1..Len(log')
                     PROVE  log'[i].hash = Mutate(log'[i].prev_hash,
                                                  log'[i].operation)
          BY DEF ASink!HashBindsContent
        <4>1. CASE i \in 1..Len(log)
          <5>1. log'[i] = log[i]
            BY <4>1, <2>ap
          <5> QED  BY <5>1, <4>1, <1>nat
                   DEF ComponentSafety, ASink!HashBindsContent
        <4>2. CASE i = Len(log) + 1
          <5>1. log'[i] = entry
            BY <4>2, <2>ap
          <5> QED  BY <5>1
        <4> QED  BY <4>1, <4>2, <2>ap, <1>nat
      <3> QED  BY <3>ci, <3>hc, <3>hb DEF ComponentSafety
    <2>8. FirstLink'
      <3> SUFFICES ASSUME Len(log') >= 1 PROVE log'[1].prev_hash = 0
        BY DEF FirstLink
      <3>1. CASE Len(log) = 0
        <4>1. log'[1] = entry
          BY <3>1, <2>ap
        <4>2. last_hash = 0
          BY <3>1, <1>nat DEF ComponentSafety, ASink!HashConsistency
        <4> QED  BY <4>1, <4>2
      <3>2. CASE Len(log) >= 1
        <4>1. log'[1] = log[1]
          BY <3>2, <2>ap, <1>nat
        <4> QED  BY <4>1, <3>2, <1>nat DEF FirstLink
      <3> QED  BY <3>1, <3>2, <1>nat
    <2> QED  BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8 DEF Inv
  (* ---- CVisit ----------------------------------------------------------- *)
  <1>2. CASE CVisit
    <2>u. log' = log /\ last_hash' = last_hash /\ c_path' = c_path
      BY <1>2 DEF CVisit
    <2>v. c_visited' = c_visited \cup {c_path}
      BY <1>2 DEF CVisit
    <2>1. c_visited' \subseteq Seq(1..BranchFactor)
      BY <2>v, <1>nat
    <2> QED  BY <2>u, <2>1, <1>nat
             DEF Inv, ComponentSafety, FirstLink,
                 ASink!ChainIntegrity, ASink!HashConsistency,
                 ASink!HashBindsContent
  <1>X. CASE Next
    BY <1>X, <1>1, <1>2 DEF Next
  <1> QED  BY <1>0, <1>X

THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv                    BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'     BY NextInv
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

(*-------------------------------------------------------------------------*)
(* Public construction invariants.                                        *)
(*-------------------------------------------------------------------------*)
THEOREM TypeSafety == Spec => []TypeInvariant
  <1>1. Inv => TypeInvariant
    BY DEF Inv, TypeInvariant, ASink!TypeInvariant
  <1> QED  BY Safety, <1>1, PTL

THEOREM ComponentSafetySafety == Spec => []ComponentSafety
  <1>1. Inv => ComponentSafety
    BY DEF Inv
  <1> QED  BY Safety, <1>1, PTL

\* O1. The token count comes from the cursor relation; the value clause comes
\* from AuditSink consistency and content binding.
THEOREM MappedPairingSafety == Spec => []MappedPairing
  <1>1. Inv => MappedPairing
    <2> SUFFICES ASSUME Inv PROVE MappedPairing
      OBVIOUS
    <2>nat. /\ log \in Seq(LogEntry)
            /\ last_hash \in Nat
            /\ Len(c_path) = Len(log)
            /\ ComponentSafety
            /\ Len(log) \in Nat
      BY LenProperties DEF Inv
    <2>lv. /\ Len(LedgerView) = Len(log)
           /\ \A i \in 1..Len(log) :
                  LedgerView[i] = [saved |-> log[i].prev_hash,
                                   delta |-> log[i].operation]
      BY <2>nat, LedgerViewProps
    <2>1. Len(LedgerView) = Len(c_path)
      BY <2>nat, <2>lv
    <2>2. Len(c_path) = 0 => AuxView = InitAux
      <3> SUFFICES ASSUME Len(c_path) = 0 PROVE AuxView = InitAux
        OBVIOUS
      <3>1. Len(log) = 0
        BY <2>nat
      <3>2. last_hash = 0
        BY <3>1, <2>nat DEF ComponentSafety, ASink!HashConsistency
      <3> QED  BY <3>2, InitAuxZero DEF AuxView
    <2>3. Len(c_path) > 0 =>
              AuxView = Mutate(LedgerView[Len(c_path)].saved,
                               LedgerView[Len(c_path)].delta)
      <3> SUFFICES ASSUME Len(c_path) > 0
                   PROVE  AuxView = Mutate(LedgerView[Len(c_path)].saved,
                                           LedgerView[Len(c_path)].delta)
        OBVIOUS
      <3>n. Len(log) > 0 /\ Len(c_path) = Len(log)
        BY <2>nat
      <3>1. last_hash = log[Len(log)].hash
        BY <3>n, <2>nat DEF ComponentSafety, ASink!HashConsistency
      <3>2. log[Len(log)].hash = Mutate(log[Len(log)].prev_hash,
                                        log[Len(log)].operation)
        BY <3>n, <2>nat DEF ComponentSafety, ASink!HashBindsContent
      <3>3. LedgerView[Len(log)] = [saved |-> log[Len(log)].prev_hash,
                                    delta |-> log[Len(log)].operation]
        BY <3>n, <2>lv
      <3> QED  BY <3>n, <3>1, <3>2, <3>3 DEF AuxView
    <2> QED  BY <2>1, <2>2, <2>3 DEF MappedPairing
  <1> QED  BY Safety, <1>1, PTL

\* O2. The recurrence is the component's chain link composed with its
\* content-binding; the anchor is Init's, carried as FirstLink.
THEOREM MappedStateRestorationSafety == Spec => []MappedStateRestoration
  <1>1. Inv => MappedStateRestoration
    <2> SUFFICES ASSUME Inv PROVE MappedStateRestoration
      OBVIOUS
    <2>nat. /\ log \in Seq(LogEntry)
            /\ ComponentSafety
            /\ FirstLink
            /\ Len(log) \in Nat
      BY LenProperties DEF Inv
    <2>lv. /\ Len(LedgerView) = Len(log)
           /\ \A i \in 1..Len(log) :
                  LedgerView[i] = [saved |-> log[i].prev_hash,
                                   delta |-> log[i].operation]
      BY <2>nat, LedgerViewProps
    <2>1. Len(LedgerView) >= 1 => LedgerView[1].saved = InitAux
      <3> SUFFICES ASSUME Len(LedgerView) >= 1
                   PROVE  LedgerView[1].saved = InitAux
        OBVIOUS
      <3>1. Len(log) >= 1
        BY <2>lv
      <3>2. LedgerView[1] = [saved |-> log[1].prev_hash,
                             delta |-> log[1].operation]
        BY <3>1, <2>lv
      <3>3. log[1].prev_hash = 0
        BY <3>1, <2>nat DEF FirstLink
      <3> QED  BY <3>2, <3>3, InitAuxZero
    <2>2. \A i \in 2..Len(LedgerView) :
              LedgerView[i].saved = Mutate(LedgerView[i-1].saved,
                                           LedgerView[i-1].delta)
      <3> SUFFICES ASSUME NEW i \in 2..Len(LedgerView)
                   PROVE  LedgerView[i].saved = Mutate(LedgerView[i-1].saved,
                                                       LedgerView[i-1].delta)
        OBVIOUS
      <3>i. i \in 2..Len(log) /\ i - 1 \in 1..Len(log)
        BY <2>lv, <2>nat
      <3>1. LedgerView[i] = [saved |-> log[i].prev_hash,
                             delta |-> log[i].operation]
        BY <3>i, <2>lv
      <3>2. LedgerView[i-1] = [saved |-> log[i-1].prev_hash,
                               delta |-> log[i-1].operation]
        BY <3>i, <2>lv
      <3>3. log[i].prev_hash = log[i-1].hash
        BY <3>i, <2>nat DEF ComponentSafety, ASink!ChainIntegrity
      <3>4. log[i-1].hash = Mutate(log[i-1].prev_hash, log[i-1].operation)
        BY <3>i, <2>nat DEF ComponentSafety, ASink!HashBindsContent
      <3> QED  BY <3>1, <3>2, <3>3, <3>4
    <2> QED  BY <2>1, <2>2 DEF MappedStateRestoration
  <1> QED  BY Safety, <1>1, PTL

(*-------------------------------------------------------------------------*)
(* The refinement. The one step with content is that appending an audit     *)
(* record appends its projected undo token -- at every index.               *)
(*-------------------------------------------------------------------------*)
LEMMA InitRefines == Init => BTU!Init
  <1> SUFFICES ASSUME Init PROVE BTU!Init
    OBVIOUS
  <1>i. log = <<>> /\ last_hash = 0
    BY DEF Init, ASink!Init
  <1>p. c_path = <<>> /\ c_visited = {}
    BY DEF Init
  <1>l. Len(log) = 0
    BY <1>i, EmptySeq
  <1>1. c_path = <<>>
    BY <1>p
  <1>2. AuxView = InitAux
    BY <1>i, InitAuxZero DEF AuxView
  <1>3. LedgerView = <<>>
    <2>1. DOMAIN LedgerView = {}
      BY <1>l DEF LedgerView
    <2>2. DOMAIN <<>> = {}
      <3>seq. <<>> \in Seq({})
        BY EmptySeq
      <3>len. Len(<<>>) = 0
        BY EmptySeq
      <3>domain. DOMAIN <<>> = 1..Len(<<>>)
        BY <3>seq, LenProperties
      <3> QED  BY <3>len, <3>domain
    <2> QED  BY <2>1, <2>2
  <1>4. c_visited = {}
    BY <1>p
  <1> QED  BY <1>1, <1>2, <1>3, <1>4 DEF BTU!Init

LEMMA NextRefines == Inv /\ [Next]_vars => [BTU!Next]_(BTU!vars)
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE [BTU!Next]_(BTU!vars)
    OBVIOUS
  <1>nat. /\ log \in Seq(LogEntry)
          /\ last_hash \in Nat
          /\ Len(log) <= MaxDepth
          /\ c_path \in Seq(1..BranchFactor)
          /\ Len(c_path) = Len(log)
          /\ Len(log) \in Nat
          /\ Len(c_path) \in Nat
    BY LenProperties DEF Inv
  <1>lv. /\ LedgerView \in Seq(LedgerEntry)
         /\ Len(LedgerView) = Len(log)
         /\ \A i \in 1..Len(log) :
                LedgerView[i] = [saved |-> log[i].prev_hash,
                                 delta |-> log[i].operation]
    BY <1>nat, LedgerViewProps
  <1>0. CASE UNCHANGED vars
    <2>1. UNCHANGED <<log, last_hash, c_path, c_visited>>
      BY <1>0 DEF vars
    <2>2. LedgerView' = LedgerView
      BY <2>1 DEF LedgerView
    <2>3. AuxView' = AuxView
      BY <2>1 DEF AuxView
    <2> QED  BY <2>1, <2>2, <2>3 DEF BTU!vars
  <1>1. CASE \E c \in 1..BranchFactor, d \in Deltas : CDescend(c, d)
    <2> SUFFICES ASSUME NEW c \in 1..BranchFactor, NEW d \in Deltas, CDescend(c, d)
                 PROVE  BTU!Next
      BY <1>1
    <2> DEFINE entry == [operation |-> d,
                         prev_hash |-> last_hash,
                         hash      |-> Mutate(last_hash, d)]
                tok   == [saved |-> last_hash, delta |-> d]
    <2>a. log' = Append(log, entry) /\ last_hash' = Mutate(last_hash, d)
      BY DEF CDescend, ASink!Record
    <2>b. c_path' = Append(c_path, c) /\ c_visited' = c_visited
      BY DEF CDescend
    <2>g. Len(c_path) # MaxDepth
      BY DEF CDescend
    <2>h. Mutate(last_hash, d) \in Nat
      BY <1>nat, MutateNat
    <2>e. entry \in LogEntry
      BY <1>nat, <2>h DEF LogEntry
    <2>t. tok \in LedgerEntry
      BY <1>nat DEF LedgerEntry
    <2>ap. /\ log' \in Seq(LogEntry)
           /\ Len(log') = Len(log) + 1
           /\ \A i \in 1..Len(log) : log'[i] = log[i]
           /\ log'[Len(log) + 1] = entry
      BY <2>a, <2>e, <1>nat, AppendProperties
    <2>al. /\ Append(LedgerView, tok) \in Seq(LedgerEntry)
           /\ Len(Append(LedgerView, tok)) = Len(LedgerView) + 1
           /\ \A i \in 1..Len(LedgerView) :
                  Append(LedgerView, tok)[i] = LedgerView[i]
           /\ Append(LedgerView, tok)[Len(LedgerView) + 1] = tok
      BY <2>t, <1>lv, AppendProperties
    \* The projection of the extended log IS the extended projection.
    <2>lv2. LedgerView' = Append(LedgerView, tok)
      \* Both sides are functions on the same domain; equality is then the
      \* pointwise comparison at <3>3. Membership in an explicit function set
      \* is what lets the backends apply extensionality.
      <3>1. LedgerView' \in [1..(Len(log) + 1) -> LedgerEntry]
        <4>1. log' \in [1..Len(log') -> LogEntry]
          BY <2>ap, LenProperties
        <4>2. Len(log') = Len(log) + 1
          BY <2>ap
        <4> QED  BY <4>1, <4>2 DEF LedgerView, LogEntry, LedgerEntry
      <3>2. Append(LedgerView, tok) \in [1..(Len(log) + 1) -> LedgerEntry]
        <4>1. Len(Append(LedgerView, tok)) = Len(log) + 1
          BY <2>al, <1>lv
        <4> QED  BY <2>al, <4>1, LenProperties
      <3>3. \A j \in 1..(Len(log) + 1) :
                LedgerView'[j] = Append(LedgerView, tok)[j]
        <4> SUFFICES ASSUME NEW j \in 1..(Len(log) + 1)
                     PROVE  LedgerView'[j] = Append(LedgerView, tok)[j]
          OBVIOUS
        <4>e. LedgerView'[j] = [saved |-> log'[j].prev_hash,
                                delta |-> log'[j].operation]
          BY <2>ap DEF LedgerView
        <4>c. j \in 1..Len(log) \/ j = Len(log) + 1
          BY <1>nat
        <4>1. CASE j \in 1..Len(log)
          <5>1. log'[j] = log[j]
            BY <4>1, <2>ap
          <5>2. LedgerView'[j] = LedgerView[j]
            BY <4>e, <5>1, <4>1, <1>lv
          <5>3. Append(LedgerView, tok)[j] = LedgerView[j]
            BY <4>1, <2>al, <1>lv
          <5> QED  BY <5>2, <5>3
        <4>2. CASE j = Len(log) + 1
          <5>1. log'[j] = entry
            BY <4>2, <2>ap
          <5>2. LedgerView'[j] = tok
            BY <4>e, <5>1
          <5>3. Append(LedgerView, tok)[j] = tok
            BY <4>2, <2>al, <1>lv
          <5> QED  BY <5>2, <5>3
        <4> QED  BY <4>c, <4>1, <4>2
      <3> QED  BY <3>1, <3>2, <3>3
    <2>aux. AuxView' = Mutate(AuxView, d)
      BY <2>a DEF AuxView
    <2>1. BTU!Descend(c, d)
      BY <2>b, <2>g, <2>lv2, <2>aux, <1>nat
      DEF BTU!Descend, BTU!IsLeaf, BTU!Depth, AuxView
    <2> QED  BY <2>1 DEF BTU!Next
  <1>2. CASE CVisit
    <2>u. log' = log /\ last_hash' = last_hash /\ c_path' = c_path
      BY <1>2 DEF CVisit
    <2>v. Len(c_path) = MaxDepth /\ c_path \notin c_visited
                                 /\ c_visited' = c_visited \cup {c_path}
      BY <1>2 DEF CVisit
    <2>1. LedgerView' = LedgerView
      BY <2>u DEF LedgerView
    <2>2. AuxView' = AuxView
      BY <2>u DEF AuxView
    <2>3. BTU!Visit
      BY <2>u, <2>v, <2>1, <2>2 DEF BTU!Visit, BTU!IsLeaf, BTU!Depth
    <2> QED  BY <2>3 DEF BTU!Next
  <1>X. CASE Next
    BY <1>X, <1>1, <1>2 DEF Next
  <1> QED  BY <1>0, <1>X

(*-------------------------------------------------------------------------*)
(* Every construction behavior maps to a BacktrackingTraversalUndo          *)
(* behavior. The construction has no target Ascend behavior.                *)
(*-------------------------------------------------------------------------*)
THEOREM Refinement == Spec => BTU!Spec
  <1>1. Init => BTU!Init                                BY InitRefines
  <1>2. Inv /\ [Next]_vars => [BTU!Next]_(BTU!vars)     BY NextRefines
  <1>3. Spec => []Inv                                   BY Safety
  <1> QED  BY <1>1, <1>2, <1>3, PTL DEF Spec, BTU!Spec

\* Restatement in the construction module's public vocabulary.
THEOREM RefinementOriginal == Spec => BacktrackingTraversalUndoRefinement
  BY Refinement DEF BacktrackingTraversalUndoRefinement

====
