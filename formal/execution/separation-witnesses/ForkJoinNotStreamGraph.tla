---- MODULE ForkJoinNotStreamGraph ----
\* Distinctness control: StreamGraph permits a record to reach the sink
\* before all source inputs have been ingested. ForkJoin's synchronization
\* barrier cannot match that observation. The expected violation of
\* AllIngestedBeforeAnyEmit supplies the separating trace.
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS MaxInputs, Capacity, RecordDomain

\* Linear topology: src -> snk (no middle so the criterion is
\* immediately observable: any sink consume before all source ingests
\* completes is the witness).
Operators == {1, 2}
Edges     == {<<1, 2>>}

Sources == {o \in Operators : \A e \in Edges : e[2] # o}
Sinks   == {o \in Operators : \A e \in Edges : e[1] # o}

InEdges(o)  == {e \in Edges : e[2] = o}
OutEdges(o) == {e \in Edges : e[1] = o}

VARIABLES queue, ingested, emitted

vars == <<queue, ingested, emitted>>

TypeInvariant ==
    /\ queue    \in [Edges -> Seq(RecordDomain)]
    /\ ingested \in 0..MaxInputs
    /\ emitted  \in 0..(MaxInputs * Cardinality(Operators))

Init ==
    /\ queue    = [e \in Edges |-> <<>>]
    /\ ingested = 0
    /\ emitted  = 0

IsEmpty(q) == Len(q) = 0
IsFull(q)  == Len(q) >= Capacity

SourceIngest(o) ==
    /\ o \in Sources
    /\ ingested < MaxInputs
    /\ \A e \in OutEdges(o) : ~IsFull(queue[e])
    /\ \E v \in RecordDomain :
        queue' = [e \in Edges |->
                    IF e \in OutEdges(o) THEN Append(queue[e], v)
                    ELSE queue[e]]
    /\ ingested' = ingested + 1
    /\ UNCHANGED emitted

SinkConsume(o) ==
    /\ o \in Sinks
    /\ \E e \in InEdges(o) : ~IsEmpty(queue[e])
    /\ LET ein == CHOOSE e \in InEdges(o) : ~IsEmpty(queue[e]) IN
         queue' = [queue EXCEPT ![ein] = Tail(queue[ein])]
    /\ emitted' = emitted + 1
    /\ UNCHANGED ingested

DoneStuttering ==
    /\ ingested = MaxInputs
    /\ \A e \in Edges : IsEmpty(queue[e])
    /\ UNCHANGED vars

Next ==
    \/ \E o \in Sources : SourceIngest(o)
    \/ \E o \in Sinks   : SinkConsume(o)
    \/ DoneStuttering

Spec == Init /\ [][Next]_vars

\* Barrier predicate expected to be violated by per-record streaming.
AllIngestedBeforeAnyEmit == (emitted > 0) => (ingested = MaxInputs)
====
