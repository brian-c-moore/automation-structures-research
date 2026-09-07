---- MODULE SelfModifyingStepGraph ----
\* Bounded candidate screen for a fixed node set with a mutable dependency
\* relation. A dependency may be added only before its target starts. The
\* target returns to NotReady, after which ordinary StepGraph eligibility
\* governs execution.
\*
\* This is not a full refinement or a general agent-loop model. It checks the
\* narrower claim that guarded edge addition preserves the defining
\* predecessor discipline of StepGraph.
EXTENDS FiniteSets

CONSTANTS Nodes, NodeStates

VARIABLES nstate, edges

vars == <<nstate, edges>>

Predecessors(n) == {p \in Nodes : <<p, n>> \in edges}

TypeInvariant ==
    /\ nstate \in [Nodes -> NodeStates]
    /\ edges \subseteq (Nodes \X Nodes)

Init ==
    /\ edges = {}
    /\ nstate = [n \in Nodes |-> "Ready"]

AddDependency(p, n) ==
    /\ p # n
    /\ <<p, n>> \notin edges
    /\ nstate[n] \in {"NotReady", "Ready"}
    /\ nstate' = [nstate EXCEPT ![n] = "NotReady"]
    /\ edges' = edges \cup {<<p, n>>}

BecomeReady(n) ==
    /\ nstate[n] = "NotReady"
    /\ \A p \in Predecessors(n) : nstate[p] = "Completed"
    /\ nstate' = [nstate EXCEPT ![n] = "Ready"]
    /\ UNCHANGED edges

StartRunning(n) ==
    /\ nstate[n] = "Ready"
    /\ nstate' = [nstate EXCEPT ![n] = "Running"]
    /\ UNCHANGED edges

CompleteNode(n) ==
    /\ nstate[n] = "Running"
    /\ nstate' = [nstate EXCEPT ![n] = "Completed"]
    /\ UNCHANGED edges

Next ==
    \/ \E p \in Nodes, n \in Nodes : AddDependency(p, n)
    \/ \E n \in Nodes : BecomeReady(n) \/ StartRunning(n) \/ CompleteNode(n)

Spec == Init /\ [][Next]_vars

ValidStates == \A n \in Nodes : nstate[n] \in NodeStates

ReadyOnlyAfterPredecessors ==
    \A n \in Nodes :
        nstate[n] = "Ready" =>
            \A p \in Predecessors(n) : nstate[p] = "Completed"

NoRunBeforePredecessors ==
    \A n \in Nodes :
        nstate[n] \in {"Running", "Completed"} =>
            \A p \in Predecessors(n) : nstate[p] = "Completed"

ThreeNodes == {1, 2, 3}
FourStates == {"NotReady", "Ready", "Running", "Completed"}
====
