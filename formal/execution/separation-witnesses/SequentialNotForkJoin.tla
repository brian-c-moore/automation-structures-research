---- MODULE SequentialNotForkJoin ----
\* Distinctness control: ForkJoin can have two workers running
\* simultaneously, an observation excluded by Sequential. The expected
\* violation of AtMostOneActive supplies the separating trace.
EXTENDS Naturals, FiniteSets

CONSTANTS Workers

\* Workers : finite set of at least 2 worker ids

VARIABLES wstate

vars == <<wstate>>

WorkerStates == {"ready", "running", "complete"}

TypeInvariant == wstate \in [Workers -> WorkerStates]

Init == wstate = [w \in Workers |-> "ready"]

Start(w) ==
    /\ wstate[w] = "ready"
    /\ wstate' = [wstate EXCEPT ![w] = "running"]

Finish(w) ==
    /\ wstate[w] = "running"
    /\ wstate' = [wstate EXCEPT ![w] = "complete"]

Next ==
    \/ \E w \in Workers : Start(w) \/ Finish(w)
    \/ (\A w \in Workers : wstate[w] = "complete") /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars

\* Sequential permits at most one active step.

NumRunning == Cardinality({w \in Workers : wstate[w] = "running"})

\* Expected violation: two ForkJoin workers can be running simultaneously.
AtMostOneActive == NumRunning <= 1
====
