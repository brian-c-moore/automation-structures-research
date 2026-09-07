---- MODULE SelfModifyingStepGraphRetroactiveDependency_NEG ----
\* Paired control for SelfModifyingStepGraph. The one disputed mechanism is
\* changed: a dependency may be added after its target has started or
\* completed, and the target state is not rolled back.
\*
\* Expected result: NoRunBeforePredecessors is violated. The counterexample
\* demonstrates that the positive model's mutation guard is load-bearing; it
\* does not classify unrestricted graph rewrite as a new execution structure.
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
    /\ edges' = edges \cup {<<p, n>>}
    /\ UNCHANGED nstate

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

NoRunBeforePredecessors ==
    \A n \in Nodes :
        nstate[n] \in {"Running", "Completed"} =>
            \A p \in Predecessors(n) : nstate[p] = "Completed"

ThreeNodes == {1, 2, 3}
FourStates == {"NotReady", "Ready", "Running", "Completed"}
====
