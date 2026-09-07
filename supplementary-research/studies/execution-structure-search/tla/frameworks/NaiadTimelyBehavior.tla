---- MODULE NaiadTimelyBehavior ----
\* ====================================================================
\* NAIAD / TIMELY DATAFLOW BEHAVIORAL SPEC (bounded study configuration)
\*
\* Behavioral property under the StreamGraph modality state machine
\* parameterized as timely dataflow (Continuous_Progress, Pointstamp_Based):
\* pointstamp values are monotonic along any path through the dataflow
\* graph. Once an operator observes a pointstamp t, no later message
\* with pointstamp < t can arrive at that operator's frontier.
\* ====================================================================
EXTENDS Naturals, Sequences, FiniteSets

\* Linear chain: op1 -> op2 -> op3.
Operators == {1, 2, 3}
Edges     == {<<1, 2>>, <<2, 3>>}

CONSTANTS MaxPointstamp

\* min_frontier[o]: minimum pointstamp this operator has emitted so far.
\* (Or undefined, modeled as -1, if the operator hasn't emitted yet.)
\* Each operator monotonically advances its frontier.
\* edge_queues hold messages tagged with pointstamps.

VARIABLES frontier, in_flight

vars == <<frontier, in_flight>>

TypeInvariant ==
    /\ frontier  \in [Operators -> 0..MaxPointstamp]
    /\ in_flight \in [Edges -> Seq(0..MaxPointstamp)]

Init ==
    /\ frontier  = [o \in Operators |-> 0]
    /\ in_flight = [e \in Edges |-> <<>>]

InEdges(o)  == {e \in Edges : e[2] = o}
OutEdges(o) == {e \in Edges : e[1] = o}
IsSource(o) == InEdges(o)  = {}
IsSink(o)   == OutEdges(o) = {}

\* Source advances its frontier and emits at the new pointstamp.
SourceEmit(o) ==
    /\ IsSource(o)
    /\ frontier[o] < MaxPointstamp
    /\ frontier' = [frontier EXCEPT ![o] = frontier[o] + 1]
    /\ in_flight' = [e \in Edges |->
                       IF e \in OutEdges(o)
                       THEN Append(in_flight[e], frontier[o] + 1)
                       ELSE in_flight[e]]

\* Middle / sink consume one message. The receiving operator's frontier
\* advances to the max of its current frontier and the incoming pointstamp.
\* This enforces the monotonicity property: an operator's frontier never
\* moves backward.
Consume(o) ==
    /\ ~IsSource(o)
    /\ \E e \in InEdges(o) : Len(in_flight[e]) > 0
    /\ LET e_in     == CHOOSE e \in InEdges(o) : Len(in_flight[e]) > 0
           ps       == Head(in_flight[e_in])
           new_fr   == IF ps > frontier[o] THEN ps ELSE frontier[o]
       IN
       /\ frontier' = [frontier EXCEPT ![o] = new_fr]
       /\ in_flight' = [e \in Edges |->
                          IF e = e_in
                          THEN Tail(in_flight[e])
                          ELSE IF e \in OutEdges(o) /\ ~IsSink(o)
                               THEN Append(in_flight[e], new_fr)
                               ELSE in_flight[e]]

DoneStuttering ==
    /\ \A o \in Operators : frontier[o] = MaxPointstamp
    /\ \A e \in Edges : Len(in_flight[e]) = 0
    /\ UNCHANGED vars

Next ==
    \/ \E o \in Operators : SourceEmit(o) \/ Consume(o)
    \/ DoneStuttering

Spec == Init /\ [][Next]_vars

\* ----- BEHAVIORAL INVARIANT -----
\* Frontier monotonicity (action property): no operator's frontier ever
\* decreases. This is the pointstamp progress guarantee from Naiad.
PointstampProgress ==
    [][\A o \in Operators : frontier'[o] >= frontier[o]]_vars

\* State invariant: pointstamps on any edge are monotonically
\* non-decreasing in queue order. Each emission appends a pointstamp
\* equal to the source operator's current (non-decreasing) frontier,
\* so the queue's sequence is sorted.
NoStaleEmission ==
    \A e \in Edges :
        \A i \in 1..(Len(in_flight[e]) - 1) :
            in_flight[e][i] <= in_flight[e][i + 1]
====
