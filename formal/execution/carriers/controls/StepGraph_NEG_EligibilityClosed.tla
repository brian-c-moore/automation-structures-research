---- MODULE StepGraph_NEG_EligibilityClosed ----
\* Negative control for EligibilityClosed. BecomeReady omits the predecessor
\* completion guard, so a node can become Ready while its predecessor remains
\* incomplete. At that state the weaker NoRunBeforePredecessors projection
\* still holds because the admitted node is not Running or Completed.

EXTENDS Integers, FiniteSets

CONSTANTS Nodes, Edges

DiamondNodes == {1, 2, 3, 4}
DiamondEdges == {<<1, 2>>, <<1, 3>>, <<2, 4>>, <<3, 4>>}

NodeStates == {"NotReady", "Ready", "Running", "Completed"}
Predecessors(n) == {p \in Nodes : <<p, n>> \in Edges}

VARIABLES nstate
vars == <<nstate>>

TypeInvariant == nstate \in [Nodes -> NodeStates]

Init ==
    nstate = [n \in Nodes |->
                IF Predecessors(n) = {} THEN "Ready" ELSE "NotReady"]

\* Fault: predecessor completion is not required.
BecomeReady(n) ==
    /\ nstate[n] = "NotReady"
    /\ Predecessors(n) # {}
    /\ nstate' = [nstate EXCEPT ![n] = "Ready"]

StartRunning(n) ==
    /\ nstate[n] = "Ready"
    /\ nstate' = [nstate EXCEPT ![n] = "Running"]

CompleteNode(n) ==
    /\ nstate[n] = "Running"
    /\ nstate' = [nstate EXCEPT ![n] = "Completed"]

AllCompleted == \A n \in Nodes : nstate[n] = "Completed"
DoneStuttering == AllCompleted /\ UNCHANGED vars

Next ==
    \/ \E n \in Nodes : BecomeReady(n) \/ StartRunning(n) \/ CompleteNode(n)
    \/ DoneStuttering

EligibilityClosed ==
    \A n \in Nodes :
        nstate[n] \in {"Ready", "Running", "Completed"} =>
            \A p \in Predecessors(n) : nstate[p] = "Completed"

NoRunBeforePredecessors ==
    \A n \in Nodes :
        (nstate[n] = "Running" \/ nstate[n] = "Completed") =>
            \A p \in Predecessors(n) : nstate[p] = "Completed"

Spec == Init /\ [][Next]_vars
====
