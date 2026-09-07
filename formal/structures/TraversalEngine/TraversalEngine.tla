---- MODULE TraversalEngine ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, RootNode, MaxBudget

VARIABLES budget_remaining, visited, accepted, queue

vars == <<budget_remaining, visited, accepted, queue>>

\* Each node costs 2 for model checking
NodeCost(n) == 2

\* Root's children are all other nodes, others have no children
NodeChildren(n) ==
    IF n = RootNode THEN Nodes \ {RootNode}
    ELSE {}

TypeInvariant ==
    /\ budget_remaining \in Nat
    /\ visited \subseteq Nodes
    /\ accepted \subseteq Nodes
    /\ queue \subseteq Nodes

\* Compatibility fact only. TypeInvariant's budget_remaining \in Nat entails
\* this predicate, so it is not an independent traversal obligation.
BudgetInvariant ==
    budget_remaining >= 0

\* Exact fixed-cost accounting for the accepted set.  Every accepted node costs
\* two units in this profile, so the initial budget must equal the remaining
\* budget plus the cost of exactly the accepted nodes.  The paired undercharge
\* control preserves natural-number typing and accepted-subset visitation while
\* violating this relation.
AcceptedCostAccounting ==
    budget_remaining + NodeCost(RootNode) * Cardinality(accepted) = MaxBudget

\* Accepted nodes are always a subset of visited nodes.
\* HELD BY CONSTRUCTION: VisitNode adds the node to visited and, in the branch
\* that accepts it, to accepted in the same step; no action adds to accepted
\* elsewhere. controls/TraversalEngine_NEG_AcceptedSubsetVisited separates
\* those effects.
AcceptedSubsetVisited ==
    accepted \subseteq visited

Init ==
    /\ budget_remaining = MaxBudget
    /\ visited = {}
    /\ accepted = {}
    /\ queue = {RootNode}

VisitNode(n) ==
    /\ n \in queue
    /\ n \notin visited
    /\ visited' = visited \cup {n}
    /\ LET nc == NodeCost(n) IN
       IF nc <= budget_remaining
       THEN /\ accepted' = accepted \cup {n}
            /\ budget_remaining' = budget_remaining - nc
            /\ queue' = (queue \ {n}) \cup NodeChildren(n)
       ELSE /\ accepted' = accepted
            /\ budget_remaining' = budget_remaining
            /\ queue' = queue \ {n}

Skip(n) ==
    /\ n \in queue
    /\ queue' = queue \ {n}
    /\ UNCHANGED <<budget_remaining, visited, accepted>>

Terminate ==
    /\ queue = {}
    /\ UNCHANGED vars

Next ==
    \/ \E n \in Nodes : VisitNode(n)
    \/ \E n \in Nodes : Skip(n)
    \/ Terminate

Spec == Init /\ [][Next]_vars

\* Spec => [](AcceptedCostAccounting /\ AcceptedSubsetVisited): proved as the
\* conjunction of AcceptedCostAccountingSafety and
\* AcceptedSubsetVisitedSafety in
\* TraversalEngine_Proof.tla.
====
