---- MODULE TraversalEngineImplRefinesSpec ----
(***************************************************************************)
(* Contract transcription for TraversalEngine. Its distinct Vec fields    *)
(* project to visited, accepted, and queue sets. num_nodes and root are    *)
(* immutable; max_budget is the constructor-profile ghost constant.         *)
(***************************************************************************)
\* EXPECT: OK
EXTENDS Naturals, FiniteSets

CONSTANTS NumNodes, RootNode, MaxBudget
ASSUME NodeCountType == NumNodes \in Nat /\ NumNodes >= 3
ASSUME RootType == RootNode \in 0..(NumNodes - 1)
ASSUME BudgetType == MaxBudget \in Nat
Nodes == 0..(NumNodes - 1)
NodeCost(n) == 2
NodeChildren(n) == IF n = RootNode THEN Nodes \ {RootNode} ELSE {}

VARIABLES num_nodes, root, max_budget,
          budget_remaining, visited, accepted, queue
vars == <<num_nodes, root, max_budget,
          budget_remaining, visited, accepted, queue>>

T == INSTANCE TraversalEngine WITH
        Nodes <- Nodes,
        RootNode <- RootNode,
        MaxBudget <- MaxBudget,
        budget_remaining <- budget_remaining,
        visited <- visited,
        accepted <- accepted,
        queue <- queue

ImplInvariant ==
    /\ num_nodes = NumNodes
    /\ root = RootNode
    /\ max_budget = MaxBudget
    /\ T!TypeInvariant
    /\ T!AcceptedCostAccounting
    /\ T!AcceptedSubsetVisited

Init ==
    /\ num_nodes = NumNodes
    /\ root = RootNode
    /\ max_budget = MaxBudget
    /\ budget_remaining = max_budget
    /\ visited = {}
    /\ accepted = {}
    /\ queue = {root}
    /\ ImplInvariant

ImplVisitNode(n) ==
    /\ ImplInvariant
    /\ n \in Nodes
    /\ n \in queue
    /\ n \notin visited
    /\ visited' = visited \cup {n}
    /\ IF NodeCost(n) <= budget_remaining
       THEN /\ accepted' = accepted \cup {n}
            /\ budget_remaining' = budget_remaining - NodeCost(n)
            /\ queue' = (queue \ {n}) \cup NodeChildren(n)
       ELSE /\ accepted' = accepted
            /\ budget_remaining' = budget_remaining
            /\ queue' = queue \ {n}
    /\ UNCHANGED <<num_nodes, root, max_budget>>
    /\ ImplInvariant'

ImplSkip(n) ==
    /\ ImplInvariant
    /\ n \in Nodes
    /\ n \in queue
    /\ queue' = queue \ {n}
    /\ UNCHANGED <<num_nodes, root, max_budget,
                    budget_remaining, visited, accepted>>
    /\ ImplInvariant'

ImplTerminateOrRead == UNCHANGED vars
ImplNext ==
    \/ \E n \in Nodes : ImplVisitNode(n)
    \/ \E n \in Nodes : ImplSkip(n)
    \/ ImplTerminateOrRead
Spec == Init /\ [][ImplNext]_vars

Refinement == T!Spec
====
