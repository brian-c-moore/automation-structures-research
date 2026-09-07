---- MODULE FlinkPipelinedBehavior ----
\* ====================================================================
\* FLINK_PIPELINED BEHAVIORAL SPEC (bounded study configuration)
\*
\* Behavioral property under the StreamGraph modality state machine
\* parameterized as Flink pipelined exchange (Continuous +
\* Declared_Anonymous + Checkpoint_Restart): backpressure activates
\* when the downstream queue reaches capacity.
\*
\* The state machine models a three-operator chain (source -> mid ->
\* sink) with bounded edge queues. The `source_blocked` flag is set
\* TRUE when the source attempts to ingest into a full src->mid queue
\* and FALSE whenever a mid_fire creates room.
\*
\* Invariant `BackpressureOnFull`:
\*   source_blocked => Len(src_to_mid) >= Capacity
\*
\* whenever the source is observed as blocked, its downstream queue
\* is at capacity; this is the operational definition of backpressure.
\* ====================================================================
EXTENDS Naturals, Sequences

CONSTANTS Capacity, MaxIngestAttempts

VARIABLES src_to_mid, mid_to_sink, source_blocked, ingest_attempts

vars == <<src_to_mid, mid_to_sink, source_blocked, ingest_attempts>>

TypeInvariant ==
    /\ src_to_mid       \in Seq({0, 1})
    /\ mid_to_sink      \in Seq({0, 1})
    /\ source_blocked   \in BOOLEAN
    /\ ingest_attempts  \in 0..MaxIngestAttempts

Init ==
    /\ src_to_mid      = <<>>
    /\ mid_to_sink     = <<>>
    /\ source_blocked  = FALSE
    /\ ingest_attempts = 0

\* Source ingest succeeds: downstream queue had room.
SourceIngestOk ==
    /\ ingest_attempts < MaxIngestAttempts
    /\ Len(src_to_mid) < Capacity
    /\ src_to_mid'      = Append(src_to_mid, 0)
    /\ source_blocked'  = FALSE
    /\ ingest_attempts' = ingest_attempts + 1
    /\ UNCHANGED mid_to_sink

\* Source ingest blocked: downstream queue is full; no record added,
\* but the attempt is recorded and the blocked flag is raised.
SourceIngestBlocked ==
    /\ ingest_attempts < MaxIngestAttempts
    /\ Len(src_to_mid) >= Capacity
    /\ source_blocked'  = TRUE
    /\ ingest_attempts' = ingest_attempts + 1
    /\ UNCHANGED <<src_to_mid, mid_to_sink>>

\* Mid drains one record. Clears source_blocked since downstream now
\* has room (preserves the BackpressureOnFull invariant).
MidFire ==
    /\ Len(src_to_mid) > 0
    /\ Len(mid_to_sink) < Capacity
    /\ src_to_mid'     = Tail(src_to_mid)
    /\ mid_to_sink'    = Append(mid_to_sink, Head(src_to_mid))
    /\ source_blocked' = FALSE
    /\ UNCHANGED ingest_attempts

\* Sink consumes one record.
SinkConsume ==
    /\ Len(mid_to_sink) > 0
    /\ mid_to_sink' = Tail(mid_to_sink)
    /\ UNCHANGED <<src_to_mid, source_blocked, ingest_attempts>>

DoneStuttering ==
    /\ ingest_attempts = MaxIngestAttempts
    /\ Len(src_to_mid) = 0
    /\ Len(mid_to_sink) = 0
    /\ UNCHANGED vars

Next ==
    \/ SourceIngestOk
    \/ SourceIngestBlocked
    \/ MidFire
    \/ SinkConsume
    \/ DoneStuttering

Spec == Init /\ [][Next]_vars

\* ----- BEHAVIORAL INVARIANT -----
\* Backpressure: source_blocked is set only when the upstream queue is
\* at capacity, and is cleared as soon as the queue has room again.
BackpressureOnFull == source_blocked => Len(src_to_mid) >= Capacity
====
