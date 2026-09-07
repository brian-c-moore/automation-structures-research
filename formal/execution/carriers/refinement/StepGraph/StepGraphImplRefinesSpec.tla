---- MODULE StepGraphImplRefinesSpec ----
(***************************************************************************)
(* Executable-contract transcription for the finite StepGraph carrier.     *)
(* The fixed topology and four state tags map to the canonical graph; each *)
(* accepted method changes exactly one node or performs the terminal step. *)
(***************************************************************************)
\* EXPECT: OK
EXTENDS Integers, FiniteSets

CONSTANTS Nodes, Edges

DiamondNodes == {1, 2, 3, 4}
DiamondEdges == {<<1, 2>>, <<1, 3>>, <<2, 4>>, <<3, 4>>}

NodeStates == {"NotReady", "Ready", "Running", "Completed"}
Predecessors(n) == {p \in Nodes : <<p, n>> \in Edges}

VARIABLES nstate
vars == <<nstate>>

TypeInvariant == nstate \in [Nodes -> NodeStates]
NoRunBeforePredecessors ==
    \A n \in Nodes :
        (nstate[n] = "Running" \/ nstate[n] = "Completed") =>
            \A p \in Predecessors(n) : nstate[p] = "Completed"
EligibilityClosed ==
    \A n \in Nodes :
        nstate[n] \in {"Ready", "Running", "Completed"} =>
            \A p \in Predecessors(n) : nstate[p] = "Completed"
ImplInvariant == TypeInvariant /\ EligibilityClosed

Init ==
    nstate = [n \in Nodes |->
                IF Predecessors(n) = {} THEN "Ready" ELSE "NotReady"]

ImplBecomeReady(n) ==
    /\ nstate[n] = "NotReady"
    /\ Predecessors(n) # {}
    /\ \A p \in Predecessors(n) : nstate[p] = "Completed"
    /\ nstate' = [nstate EXCEPT ![n] = "Ready"]

ImplStartRunning(n) ==
    /\ nstate[n] = "Ready"
    /\ nstate' = [nstate EXCEPT ![n] = "Running"]

ImplCompleteNode(n) ==
    /\ nstate[n] = "Running"
    /\ nstate' = [nstate EXCEPT ![n] = "Completed"]

ImplDoneStuttering ==
    /\ \A n \in Nodes : nstate[n] = "Completed"
    /\ UNCHANGED vars

ImplNext ==
    \/ \E n \in Nodes : ImplBecomeReady(n)
    \/ \E n \in Nodes : ImplStartRunning(n)
    \/ \E n \in Nodes : ImplCompleteNode(n)
    \/ ImplDoneStuttering

S == INSTANCE StepGraph WITH
        Nodes <- Nodes,
        Edges <- Edges,
        nstate <- nstate

Spec == Init /\ [][ImplNext]_vars
Refinement == S!Spec
====
