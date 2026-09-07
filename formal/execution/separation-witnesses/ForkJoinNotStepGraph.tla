---- MODULE ForkJoinNotStepGraph ----
\* Distinctness control: a three-node StepGraph can start a downstream
\* node after its predecessor completes while other graph work remains.
\* ForkJoin's barrier semantics cannot match that chained mid-execution
\* handoff. The expected violation of NoCompletedAndRunningBoth supplies
\* the separating trace.
EXTENDS Naturals, FiniteSets

Nodes == {1, 2, 3}
Edges == {<<1, 2>>, <<2, 3>>}

NodeStates == {"NotReady", "Ready", "Running", "Completed"}

Predecessors(n) == {p \in Nodes : <<p, n>> \in Edges}

VARIABLES nstate

vars == <<nstate>>

TypeInvariant == nstate \in [Nodes -> NodeStates]

Init ==
    nstate = [n \in Nodes |->
                IF Predecessors(n) = {} THEN "Ready" ELSE "NotReady"]

BecomeReady(n) ==
    /\ nstate[n] = "NotReady"
    /\ \A p \in Predecessors(n) : nstate[p] = "Completed"
    /\ nstate' = [nstate EXCEPT ![n] = "Ready"]

StartRunning(n) ==
    /\ nstate[n] = "Ready"
    /\ nstate' = [nstate EXCEPT ![n] = "Running"]

CompleteNode(n) ==
    /\ nstate[n] = "Running"
    /\ nstate' = [nstate EXCEPT ![n] = "Completed"]

Next ==
    \/ \E n \in Nodes : BecomeReady(n) \/ StartRunning(n) \/ CompleteNode(n)
    \/ (\A n \in Nodes : nstate[n] = "Completed") /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars

\* Separating predicate: no node is Running while an immediate predecessor
\* is Completed. It holds for barrier-synchronized ForkJoin behavior and is
\* violated by the chained StepGraph execution above.
NoCompletedAndRunningBoth ==
    ~(\E p, n \in Nodes :
        /\ <<p, n>> \in Edges
        /\ nstate[p] = "Completed"
        /\ nstate[n] = "Running")
====
