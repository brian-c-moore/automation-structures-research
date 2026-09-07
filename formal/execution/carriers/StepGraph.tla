---- MODULE StepGraph ----
\* Step-based graph carrier: each node runs to completion before its
\* downstream nodes become eligible. EligibilityClosed is the primary
\* eligibility clause, NoRunBeforePredecessors is its derived projection, and
\* ProgressMonotonic checks that node states do not regress.
\*
\* PARAMETERIZED OVER AN INPUT GRAPH. The body refers to the CONSTANTs Nodes and
\* Edges, and a .cfg binds a topology by DEFINITION SUBSTITUTION --
\* `Edges <- DiamondEdges` -- rather than by a literal value, so the tuples stay
\* inside TLA+, where they are legal, and the .cfg value parser never sees one.
\*
\* No ASSUME constrains the substituted graph. StepGraph_Proof is parametric in
\* Nodes and Edges and does not claim graph well-formedness beyond the written
\* state and eligibility predicates.
EXTENDS Integers, FiniteSets

CONSTANTS Nodes, Edges

\* Concrete topologies, for .cfg substitution: StepGraph.cfg binds Diamond and
\* StepGraph_Linear.cfg binds Linear.
DiamondNodes == {1, 2, 3, 4}          \* 1 -> {2, 3} -> 4
DiamondEdges == {<<1, 2>>, <<1, 3>>, <<2, 4>>, <<3, 4>>}
LinearNodes  == {1, 2, 3, 4}          \* 1 -> 2 -> 3 -> 4
LinearEdges  == {<<1, 2>>, <<2, 3>>, <<3, 4>>}

NodeStates == {"NotReady", "Ready", "Running", "Completed"}

Predecessors(n) == {p \in Nodes : <<p, n>> \in Edges}
Successors(n)   == {s \in Nodes : <<n, s>> \in Edges}

Rank(s) ==
    CASE s = "NotReady"  -> 0
      [] s = "Ready"     -> 1
      [] s = "Running"   -> 2
      [] s = "Completed" -> 3
      [] OTHER           -> -1

VARIABLES nstate

vars == <<nstate>>

TypeInvariant == nstate \in [Nodes -> NodeStates]

Init ==
    nstate = [n \in Nodes |->
                IF Predecessors(n) = {} THEN "Ready" ELSE "NotReady"]

BecomeReady(n) ==
    /\ nstate[n] = "NotReady"
    /\ Predecessors(n) # {}
    /\ \A p \in Predecessors(n) : nstate[p] = "Completed"
    /\ nstate' = [nstate EXCEPT ![n] = "Ready"]

StartRunning(n) ==
    /\ nstate[n] = "Ready"
    /\ nstate' = [nstate EXCEPT ![n] = "Running"]

CompleteNode(n) ==
    /\ nstate[n] = "Running"
    /\ nstate' = [nstate EXCEPT ![n] = "Completed"]

AllCompleted == \A n \in Nodes : nstate[n] = "Completed"

DoneStuttering ==
    /\ AllCompleted
    /\ UNCHANGED vars

Next ==
    \/ \E n \in Nodes : BecomeReady(n) \/ StartRunning(n) \/ CompleteNode(n)
    \/ DoneStuttering

Spec == Init /\ [][Next]_vars

\* Every admitted state beyond NotReady requires completed predecessors.
EligibilityClosed ==
    \A n \in Nodes :
        nstate[n] \in {"Ready", "Running", "Completed"} =>
            \A p \in Predecessors(n) : nstate[p] = "Completed"

\* Derived from EligibilityClosed by restricting the antecedent.
NoRunBeforePredecessors ==
    \A n \in Nodes :
        (nstate[n] = "Running" \/ nstate[n] = "Completed") =>
            \A p \in Predecessors(n) : nstate[p] = "Completed"

\* Graph progress monotonicity, expressed as an action property.
ProgressMonotonic ==
    [][\A n \in Nodes : Rank(nstate'[n]) >= Rank(nstate[n])]_vars

ValidStates == \A n \in Nodes : nstate[n] \in NodeStates
====
