---- MODULE StreamGraphImplRefinesSpec ----
(***************************************************************************)
(* Executable-contract transcription for the finite linear StreamGraph.    *)
(* The three queues and two counters map directly to the canonical carrier *)
(* for the retained three- and four-node chain profiles.                    *)
(***************************************************************************)
\* EXPECT: OK
EXTENDS Naturals, Sequences

CONSTANTS Capacity, MaxInputs, RecordDomain, ChainLength
ASSUME CapacityType == Capacity \in Nat /\ Capacity > 0
ASSUME MaxInputsType == MaxInputs \in Nat
ASSUME RecordDomainNonEmpty == RecordDomain # {}
ASSUME RetainedChainLength == ChainLength \in {3, 4}

VARIABLES q1, q2, q3, ingested, emitted
vars == <<q1, q2, q3, ingested, emitted>>

TypeInvariant ==
    /\ q1 \in Seq(RecordDomain)
    /\ q2 \in Seq(RecordDomain)
    /\ q3 \in Seq(RecordDomain)
    /\ ChainLength = 3 => q3 = <<>>
    /\ ingested \in 0..MaxInputs
    /\ emitted \in 0..MaxInputs
IsFull(q) == Len(q) >= Capacity
IsEmpty(q) == Len(q) = 0
BackpressureCorrect ==
    /\ Len(q1) <= Capacity
    /\ Len(q2) <= Capacity
    /\ ChainLength = 4 => Len(q3) <= Capacity
QueueDepth ==
    IF ChainLength = 3
    THEN Len(q1) + Len(q2)
    ELSE Len(q1) + Len(q2) + Len(q3)
OccupancyCountConservation == ingested = QueueDepth + emitted
NoRecordLoss == OccupancyCountConservation
ImplInvariant == TypeInvariant /\ BackpressureCorrect /\ OccupancyCountConservation

Init ==
    /\ q1 = <<>>
    /\ q2 = <<>>
    /\ q3 = <<>>
    /\ ingested = 0
    /\ emitted = 0

ImplSourceIngest(v) ==
    /\ ingested < MaxInputs
    /\ ~IsFull(q1)
    /\ v \in RecordDomain
    /\ q1' = Append(q1, v)
    /\ ingested' = ingested + 1
    /\ UNCHANGED <<q2, q3, emitted>>

ImplMiddle2Fire ==
    /\ ~IsEmpty(q1)
    /\ ~IsFull(q2)
    /\ q1' = Tail(q1)
    /\ q2' = Append(q2, Head(q1))
    /\ UNCHANGED <<q3, ingested, emitted>>

ImplMiddle3Fire ==
    /\ ChainLength = 4
    /\ ~IsEmpty(q2)
    /\ ~IsFull(q3)
    /\ q2' = Tail(q2)
    /\ q3' = Append(q3, Head(q2))
    /\ UNCHANGED <<q1, ingested, emitted>>

ImplSinkConsume3 ==
    /\ ChainLength = 3
    /\ ~IsEmpty(q2)
    /\ q2' = Tail(q2)
    /\ emitted' = emitted + 1
    /\ UNCHANGED <<q1, q3, ingested>>

ImplSinkConsume4 ==
    /\ ChainLength = 4
    /\ ~IsEmpty(q3)
    /\ q3' = Tail(q3)
    /\ emitted' = emitted + 1
    /\ UNCHANGED <<q1, q2, ingested>>

ImplDoneStuttering ==
    /\ ingested = MaxInputs
    /\ IsEmpty(q1) /\ IsEmpty(q2) /\ IsEmpty(q3)
    /\ UNCHANGED vars

ImplNext ==
    \/ \E v \in RecordDomain : ImplSourceIngest(v)
    \/ ImplMiddle2Fire
    \/ ImplMiddle3Fire
    \/ ImplSinkConsume3
    \/ ImplSinkConsume4
    \/ ImplDoneStuttering

G == INSTANCE StreamGraph WITH
        Capacity <- Capacity,
        MaxInputs <- MaxInputs,
        RecordDomain <- RecordDomain,
        ChainLength <- ChainLength,
        q1 <- q1,
        q2 <- q2,
        q3 <- q3,
        ingested <- ingested,
        emitted <- emitted

Spec == Init /\ [][ImplNext]_vars
Refinement == G!Spec
====
