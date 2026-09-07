---- MODULE TraversalBudgetComposition_NEG_CompositionInvariant ----
\* NEGATIVE CONTROL, generated. Not a specification: this is TraversalBudgetComposition
\* carrying one deliberate defect, so that a checker fails on it.
\*
\*   base module      : TraversalBudgetComposition
\*   mutation site    : VisitAndAccept
\*   target           : CompositionInvariant
\*   required outcome : with only CompositionInvariant declared, TLC MUST report the invariant
\*                      violated. A run that finds no error is a control that has
\*                      stopped measuring.
\*
\* The mutation is delimited by the markers below. Outside them, and
\* apart from the module name, this file is TraversalBudgetComposition verbatim, less
\* that module's commentary.

EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, RootNode, MaxBudget

VARIABLES accepted, total_cost, budget_remaining, visited, queue

vars == <<accepted, total_cost, budget_remaining, visited, queue>>

NodeCost(n) == 2

NodeChildren(n) ==
    IF n = RootNode THEN Nodes \ {RootNode}
    ELSE {}

TypeInvariant ==
    /\ accepted \subseteq Nodes
    /\ total_cost \in 0..MaxBudget
    /\ budget_remaining \in 0..MaxBudget
    /\ visited \subseteq Nodes
    /\ queue \subseteq Nodes

CompositionInvariant ==
    /\ total_cost <= MaxBudget
    /\ total_cost + budget_remaining = MaxBudget

AcceptedSubsetVisited == accepted \subseteq visited

Init ==
    /\ accepted = {}
    /\ total_cost = 0
    /\ budget_remaining = MaxBudget
    /\ visited = {}
    /\ queue = {RootNode}

VisitAndAccept(n) ==
    /\ n \in queue
    /\ n \notin visited
\* ---- MUTATION BEGINS -- to the closing marker, this replaces the base text.
    /\ accepted'         = accepted \cup {n}
\* ---- MUTATION ENDS.
    /\ total_cost'       = total_cost + NodeCost(n)
    /\ budget_remaining' = budget_remaining - NodeCost(n)
    /\ visited'          = visited \cup {n}
    /\ queue'            = (queue \ {n}) \cup NodeChildren(n)

SkipUnaffordable(n) ==
    /\ n \in queue
    /\ n \notin visited
    /\ NodeCost(n) > budget_remaining
    /\ visited' = visited \cup {n}
    /\ queue'   = queue \ {n}
    /\ UNCHANGED <<accepted, total_cost, budget_remaining>>

Skip(n) ==
    /\ n \in queue
    /\ queue' = queue \ {n}
    /\ UNCHANGED <<accepted, total_cost, budget_remaining, visited>>

Terminate ==
    /\ queue = {}
    /\ UNCHANGED vars

Next ==
    \/ \E n \in Nodes : VisitAndAccept(n)
    \/ \E n \in Nodes : SkipUnaffordable(n)
    \/ \E n \in Nodes : Skip(n)
    \/ Terminate

Spec == Init /\ [][Next]_vars

====
