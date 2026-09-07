---------------------- MODULE TraversalEngineDecomposed ----------------------
(* Splits TraversalEngine's VisitNode: EvaluateNode holds its membership and
   budget tests (`NodeCost(n) <= budget_remaining`); AcceptNode applies its
   writes on the held outcome. Two traversers evaluate one node with budget for
   one and both pay, so budget_remaining goes below zero, violating
   BudgetInvariant (the .cfg lists it before TypeInvariant, whose `\in Nat`
   fails at the same state). Adds `pc`, `held`, and a second traverser. *)
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, RootNode, MaxBudget

VARIABLES budget_remaining, visited, accepted, queue, pc, held

vars == <<budget_remaining, visited, accepted, queue, pc, held>>

Procs == {"p1", "p2"}

NodeCost(n) == 2

NodeChildren(n) ==
    IF n = RootNode THEN Nodes \ {RootNode}
    ELSE {}

TypeInvariant ==
    /\ budget_remaining \in Nat
    /\ visited \subseteq Nodes
    /\ accepted \subseteq Nodes
    /\ queue \subseteq Nodes

BudgetInvariant ==
    budget_remaining >= 0

AcceptedSubsetVisited ==
    accepted \subseteq visited

Init ==
    /\ budget_remaining = MaxBudget
    /\ visited = {}
    /\ accepted = {}
    /\ queue = {RootNode}
    /\ pc = [p \in Procs |-> "idle"]
    /\ held = [p \in Procs |-> [node |-> RootNode, fits |-> FALSE]]

(* Step 1: canonical VisitNode's tests -- membership and the budget test --
   with the node and the test's outcome held; no mutation *)
EvaluateNode(p, n) ==
    /\ pc[p] = "idle"
    /\ n \in queue
    /\ n \notin visited
    /\ held' = [held EXCEPT ![p] = [node |-> n, fits |-> NodeCost(n) <= budget_remaining]]
    /\ pc' = [pc EXCEPT ![p] = "evaluated"]
    /\ UNCHANGED <<budget_remaining, visited, accepted, queue>>

(* Step 2: canonical VisitNode's writes, both branches, on the held outcome *)
AcceptNode(p) ==
    /\ pc[p] = "evaluated"
    /\ LET n == held[p].node
           nc == NodeCost(n) IN
       /\ visited' = visited \cup {n}
       /\ IF held[p].fits
          THEN /\ accepted' = accepted \cup {n}
               /\ budget_remaining' = budget_remaining - nc
               /\ queue' = (queue \ {n}) \cup NodeChildren(n)
          ELSE /\ accepted' = accepted
               /\ budget_remaining' = budget_remaining
               /\ queue' = queue \ {n}
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED held

Skip(n) ==
    /\ n \in queue
    /\ queue' = queue \ {n}
    /\ UNCHANGED <<budget_remaining, visited, accepted, pc, held>>

Terminate ==
    /\ queue = {}
    /\ UNCHANGED vars

Next ==
    \/ \E p \in Procs, n \in Nodes : EvaluateNode(p, n)
    \/ \E p \in Procs : AcceptNode(p)
    \/ \E n \in Nodes : Skip(n)
    \/ Terminate

Spec == Init /\ [][Next]_vars
=============================================================================
