---- MODULE StreamGraph ----
\* Linear-chain streaming carrier for the specified three- and four-operator
\* validation configurations. This is intentionally not an arbitrary graph:
\* conservation under fan-out needs multiplicity accounting that is outside
\* the current claim. q1, q2, and q3 are the consecutive edge queues; q3 is
\* fixed empty in the three-operator configuration.
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

Init ==
    /\ q1 = <<>>
    /\ q2 = <<>>
    /\ q3 = <<>>
    /\ ingested = 0
    /\ emitted = 0

IsFull(q) == Len(q) >= Capacity
IsEmpty(q) == Len(q) = 0

SourceIngest ==
    /\ ingested < MaxInputs
    /\ ~IsFull(q1)
    /\ \E v \in RecordDomain : q1' = Append(q1, v)
    /\ ingested' = ingested + 1
    /\ UNCHANGED <<q2, q3, emitted>>

Middle2Fire ==
    /\ ~IsEmpty(q1)
    /\ ~IsFull(q2)
    /\ q1' = Tail(q1)
    /\ q2' = Append(q2, Head(q1))
    /\ UNCHANGED <<q3, ingested, emitted>>

Middle3Fire ==
    /\ ChainLength = 4
    /\ ~IsEmpty(q2)
    /\ ~IsFull(q3)
    /\ q2' = Tail(q2)
    /\ q3' = Append(q3, Head(q2))
    /\ UNCHANGED <<q1, ingested, emitted>>

MiddleFire(o) ==
    \/ o = 2 /\ Middle2Fire
    \/ o = 3 /\ Middle3Fire

SinkConsume3 ==
    /\ ChainLength = 3
    /\ ~IsEmpty(q2)
    /\ q2' = Tail(q2)
    /\ emitted' = emitted + 1
    /\ UNCHANGED <<q1, q3, ingested>>

SinkConsume4 ==
    /\ ChainLength = 4
    /\ ~IsEmpty(q3)
    /\ q3' = Tail(q3)
    /\ emitted' = emitted + 1
    /\ UNCHANGED <<q1, q2, ingested>>

SinkConsume == SinkConsume3 \/ SinkConsume4

DoneStuttering ==
    /\ ingested = MaxInputs
    /\ IsEmpty(q1) /\ IsEmpty(q2) /\ IsEmpty(q3)
    /\ UNCHANGED vars

Next ==
    \/ SourceIngest
    \/ Middle2Fire
    \/ Middle3Fire
    \/ SinkConsume3
    \/ SinkConsume4
    \/ DoneStuttering

Spec == Init /\ [][Next]_vars

BackpressureCorrect ==
    /\ Len(q1) <= Capacity
    /\ Len(q2) <= Capacity
    /\ ChainLength = 4 => Len(q3) <= Capacity

QueueDepth ==
    IF ChainLength = 3
    THEN Len(q1) + Len(q2)
    ELSE Len(q1) + Len(q2) + Len(q3)

OccupancyCountConservation == ingested = QueueDepth + emitted

\* Compatibility alias only. Scalar occupancy accounting cannot distinguish a
\* lost record paired with a duplicate and does not establish durability or
\* exactly-once delivery.
NoRecordLoss == OccupancyCountConservation

SomeActionEnabled ==
    \/ (ingested < MaxInputs /\ ~IsFull(q1))
    \/ (~IsEmpty(q1) /\ ~IsFull(q2))
    \/ (ChainLength = 4 /\ ~IsEmpty(q2) /\ ~IsFull(q3))
    \/ (ChainLength = 3 /\ ~IsEmpty(q2))
    \/ (ChainLength = 4 /\ ~IsEmpty(q3))
    \/ (ingested = MaxInputs /\ IsEmpty(q1) /\ IsEmpty(q2) /\ IsEmpty(q3))

\* State-level action enabledness, not temporal liveness or scheduler fairness.
\* Compatibility identifier only; the formula is state-level action enabledness.
DeadlockFreedom == SomeActionEnabled
====
