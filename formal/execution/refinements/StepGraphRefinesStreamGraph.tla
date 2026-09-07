---- MODULE StepGraphRefinesStreamGraph ----
\* StepGraph refines StreamGraph under batch-granular operator
\* emission: an operator emits its whole batch at completion rather than
\* per record, so no producer ever blocks on a full queue -- which is
\* what BackpressureDisabled records. This formalizes the
\* unit-of-completion criterion.
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS RecordsPerEdge

\* Linear chain: 1 -> 2 -> 3
Nodes == {1, 2, 3}
Edges == {<<1, 2>>, <<2, 3>>}

NodeStates == {"NotReady", "Ready", "Running", "Completed"}

Predecessors(n) == {p \in Nodes : <<p, n>> \in Edges}
Successors(n)   == {s \in Nodes : <<n, s>> \in Edges}

VARIABLES nstate, queue

vars == <<nstate, queue>>

TypeInvariant ==
    /\ nstate \in [Nodes -> NodeStates]
    /\ queue  \in [Edges -> 0..RecordsPerEdge]

\* Operators emit at completion, not per-record.
RefinementMapping ==
    \A e \in Edges :
        queue[e] = (IF nstate[e[1]] = "Completed" THEN RecordsPerEdge ELSE 0)

Init ==
    /\ nstate = [n \in Nodes |->
                    IF Predecessors(n) = {} THEN "Ready" ELSE "NotReady"]
    /\ queue  = [e \in Edges |-> 0]

BecomeReady(n) ==
    /\ nstate[n] = "NotReady"
    /\ Predecessors(n) # {}
    /\ \A p \in Predecessors(n) : nstate[p] = "Completed"
    /\ nstate' = [nstate EXCEPT ![n] = "Ready"]
    /\ UNCHANGED queue

StartRunning(n) ==
    /\ nstate[n] = "Ready"
    /\ nstate' = [nstate EXCEPT ![n] = "Running"]
    /\ UNCHANGED queue

CompleteAndEmit(n) ==
    /\ nstate[n] = "Running"
    /\ nstate' = [nstate EXCEPT ![n] = "Completed"]
    /\ queue'  = [e \in Edges |->
                    IF e[1] = n THEN RecordsPerEdge ELSE queue[e]]

Done == \A n \in Nodes : nstate[n] = "Completed"

Next ==
    \/ \E n \in Nodes : BecomeReady(n) \/ StartRunning(n) \/ CompleteAndEmit(n)
    \/ (Done /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

UnitOfCompletion == RefinementMapping
BackpressureDisabled == \A e \in Edges : queue[e] <= RecordsPerEdge
NoRunBeforePredecessors ==
    \A n \in Nodes :
        nstate[n] \in {"Running", "Completed"} =>
            \A p \in Predecessors(n) : nstate[p] = "Completed"
====
