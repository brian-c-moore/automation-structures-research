---- MODULE TraversalEngine_NEG_AcceptedCostAccounting ----
\* NEGATIVE CONTROL. Not a specification: this is TraversalEngine carrying
\* one deliberate undercharge, so that a checker fails on the exact accepted-
\* cost relation while natural-number typing and accepted-subset visitation
\* continue to hold.
\*
\*   base module      : TraversalEngine
\*   mutation site    : VisitNode accepted branch
\*   target           : AcceptedCostAccounting
\*   required outcome : with only AcceptedCostAccounting declared, TLC MUST
\*                      report the invariant violated.

EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, RootNode, MaxBudget

VARIABLES budget_remaining, visited, accepted, queue

vars == <<budget_remaining, visited, accepted, queue>>

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

AcceptedCostAccounting ==
    budget_remaining + NodeCost(RootNode) * Cardinality(accepted) = MaxBudget

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
\* ---- MUTATION BEGINS -- undercharge an accepted node by one unit.
            /\ budget_remaining' = budget_remaining - 1
\* ---- MUTATION ENDS.
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

====
