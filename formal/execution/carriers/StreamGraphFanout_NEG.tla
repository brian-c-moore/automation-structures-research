---- MODULE StreamGraphFanout_NEG ----
\* Falsifier for scalar occupancy-count conservation on fan-out.
\* The source has two out-edges and Middle is empty, so
\* LinearGraphAssumption is vacuously TRUE. One SourceIngest broadcasts one
\* record to both edges while incrementing ingested once; the scalar equation
\* must therefore be violated. This control shows a theorem-boundary defect.
\* It does not claim that fan-out streaming is wrong.
EXTENDS Naturals, Sequences, FiniteSets

Operators == {1, 2, 3}
Edges == {<<1, 2>>, <<1, 3>>}
RecordDomain == {0}

Sources == {o \in Operators : \A e \in Edges : e[2] # o}
Sinks   == {o \in Operators : \A e \in Edges : e[1] # o}
Middle  == Operators \ (Sources \cup Sinks)
InEdges(o)  == {e \in Edges : e[2] = o}
OutEdges(o) == {e \in Edges : e[1] = o}

VARIABLES queue, ingested, emitted
vars == <<queue, ingested, emitted>>

Init ==
    /\ queue = [e \in Edges |-> <<>>]
    /\ ingested = 0
    /\ emitted = 0

SourceIngest ==
    /\ \E v \in RecordDomain :
         queue' = [e \in Edges |->
                     IF e \in OutEdges(1) THEN Append(queue[e], v) ELSE queue[e]]
    /\ ingested' = ingested + 1
    /\ UNCHANGED emitted

Next == SourceIngest
Spec == Init /\ [][Next]_vars

RECURSIVE SumQueueLen(_)
SumQueueLen(eset) ==
    IF eset = {} THEN 0
    ELSE LET e == CHOOSE x \in eset : TRUE
         IN Len(queue[e]) + SumQueueLen(eset \ {e})

QueueDepth == SumQueueLen(Edges)

\* This antecedent constrains only Middle, which is empty.
LinearGraphAssumption ==
    \A o \in Middle :
        Cardinality(InEdges(o)) = 1 /\ Cardinality(OutEdges(o)) = 1

ScalarOccupancyCountConservation ==
    LinearGraphAssumption => (ingested = QueueDepth + emitted)
====
