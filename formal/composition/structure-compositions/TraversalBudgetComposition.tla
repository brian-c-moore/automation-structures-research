---- MODULE TraversalBudgetComposition ----
\* Coupled TraversalEngine and Budget state machine. Its safety contract is:
\*   /\ TraversalEngine!Spec
\*   /\ Budget!Spec
\*   /\ TraversalEngine!budget_remaining = Budget!capacity - Budget!allocated
\*   => [](AllocationSnapshot!total_cost <= Budget!capacity)
\*
\* The two modules are coupled by a shared budget: every node acceptance
\* deducts from both. That coupling is realised here as a single state
\* machine where total_cost (the AllocationSnapshot view) and
\* budget_remaining (the Budget view) move together. The composition
\* invariant is the bookkeeping equation:
\*   total_cost + budget_remaining = MaxBudget
\* together with the safety bound total_cost <= MaxBudget.

EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, RootNode, MaxBudget

VARIABLES accepted, total_cost, budget_remaining, visited, queue

vars == <<accepted, total_cost, budget_remaining, visited, queue>>

\* Cost and child shape match the standalone TraversalEngine carrier.
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

\* The composition invariant: snapshot total bounded by capacity AND
\* the two views agree (no resource appears or disappears).
CompositionInvariant ==
    /\ total_cost <= MaxBudget
    /\ total_cost + budget_remaining = MaxBudget

\* Inherited from TraversalEngine: every accepted node was visited.
AcceptedSubsetVisited == accepted \subseteq visited

Init ==
    /\ accepted = {}
    /\ total_cost = 0
    /\ budget_remaining = MaxBudget
    /\ visited = {}
    /\ queue = {RootNode}

\* Atomic visit-accept-deduct: the guard, acceptance, traversal update, and
\* dual budget bookkeeping commit in one step.
VisitAndAccept(n) ==
    /\ n \in queue
    /\ n \notin visited
    /\ NodeCost(n) <= budget_remaining
    /\ accepted'         = accepted \cup {n}
    /\ total_cost'       = total_cost + NodeCost(n)
    /\ budget_remaining' = budget_remaining - NodeCost(n)
    /\ visited'          = visited \cup {n}
    /\ queue'            = (queue \ {n}) \cup NodeChildren(n)

\* Visit-but-skip: cost overruns -- mark visited (so the node is not
\* re-entered) but do NOT accept and do NOT deduct.
SkipUnaffordable(n) ==
    /\ n \in queue
    /\ n \notin visited
    /\ NodeCost(n) > budget_remaining
    /\ visited' = visited \cup {n}
    /\ queue'   = queue \ {n}
    /\ UNCHANGED <<accepted, total_cost, budget_remaining>>

\* Pure skip: drop a queued node without visiting (still possible because
\* the traversal engine is allowed to make heuristic choices).
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

\* Spec => [](TypeInvariant /\ CompositionInvariant /\ AcceptedSubsetVisited):
\* proved as the conjunction of TypeSafety, CompositionSafety,
\* AcceptedSubsetVisitedSafety in TraversalBudgetComposition_Proof.tla.
====
