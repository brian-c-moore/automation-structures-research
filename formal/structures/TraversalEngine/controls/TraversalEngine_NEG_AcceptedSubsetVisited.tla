---- MODULE TraversalEngine_NEG_AcceptedSubsetVisited ----
\* NEGATIVE CONTROL, generated. Not a specification: this is TraversalEngine
\* carrying one deliberate defect, so that a checker fails on it.
\*
\*   base module      : TraversalEngine
\*   mutation site    : VisitNode
\*   target           : AcceptedSubsetVisited
\*   required outcome : with only AcceptedSubsetVisited declared, TLC MUST report the invariant
\*                      violated. A run that finds no error is a control that has
\*                      stopped measuring.
\*
\* The mutation is delimited by the markers below. Outside them, and
\* apart from the module name, this file is TraversalEngine verbatim, less
\* that module's commentary.

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

AcceptedSubsetVisited ==
    accepted \subseteq visited

Init ==
    /\ budget_remaining = MaxBudget
    /\ visited = {}
    /\ accepted = {}
    /\ queue = {RootNode}

VisitNode(n) ==
    /\ n \in queue
\* ---- MUTATION BEGINS -- to the closing marker, this replaces the base text.
    /\ n \notin visited
    /\ visited' = visited
\* ---- MUTATION ENDS.
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

====
