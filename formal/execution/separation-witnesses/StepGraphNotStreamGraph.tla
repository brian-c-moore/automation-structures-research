---- MODULE StepGraphNotStreamGraph ----
\* Distinctness control: a two-operator StreamGraph can deliver a record
\* downstream before the source finishes. StepGraph's unit-completion
\* semantics exclude that observation. The expected violation of
\* DownstreamOnlyAfterUpstreamCompletes supplies the separating trace.
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS MaxInputs, Capacity

Edges     == {<<1, 2>>}

VARIABLES queue, ingested, emitted, source_done

vars == <<queue, ingested, emitted, source_done>>

TypeInvariant ==
    /\ queue       \in [Edges -> Seq({0, 1})]
    /\ ingested    \in 0..MaxInputs
    /\ emitted     \in 0..MaxInputs
    /\ source_done \in BOOLEAN

Init ==
    /\ queue       = [e \in Edges |-> <<>>]
    /\ ingested    = 0
    /\ emitted     = 0
    /\ source_done = FALSE

SourceIngest ==
    /\ ingested < MaxInputs
    /\ Len(queue[<<1, 2>>]) < Capacity
    /\ \E v \in {0, 1} :
        queue' = [queue EXCEPT ![<<1, 2>>] = Append(queue[<<1, 2>>], v)]
    /\ ingested' = ingested + 1
    /\ UNCHANGED <<emitted, source_done>>

SourceFinish ==
    /\ ingested = MaxInputs
    /\ ~source_done
    /\ source_done' = TRUE
    /\ UNCHANGED <<queue, ingested, emitted>>

SinkConsume ==
    /\ Len(queue[<<1, 2>>]) > 0
    /\ queue'   = [queue EXCEPT ![<<1, 2>>] = Tail(queue[<<1, 2>>])]
    /\ emitted' = emitted + 1
    /\ UNCHANGED <<ingested, source_done>>

DoneStuttering ==
    /\ source_done
    /\ Len(queue[<<1, 2>>]) = 0
    /\ UNCHANGED vars

Next == SourceIngest \/ SourceFinish \/ SinkConsume \/ DoneStuttering

Spec == Init /\ [][Next]_vars

\* StepGraph predicate expected to be violated by per-record streaming.
DownstreamOnlyAfterUpstreamCompletes ==
    (emitted > 0) => source_done
====
