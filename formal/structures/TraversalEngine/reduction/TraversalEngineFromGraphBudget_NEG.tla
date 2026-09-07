---- MODULE TraversalEngineFromGraphBudget_NEG ----
\* NEGATIVE CONTROL for TraversalEngineFromGraphBudget. Identical EXCEPT
\* VisitNode's accept branch admits the node and expands the frontier
\* WITHOUT charging the Budget (the TryAllocate half of the atomic
\* visit+deduct is omitted). Every carried invariant still holds -- the
\* Budget stays legal (its allocation never grows), the graph invariants
\* are untouched, so the fault is invisible to invariant
\* checking. It can only be caught by the refinement property: the step
\* grows accepted while the mapped budget_remaining stays frozen, matching
\* neither TraversalEngine!VisitNode branch (accept deducts NodeCost = 2;
\* reject leaves accepted unchanged) nor Skip (visited grew) nor a
\* stutter. The paired configuration must therefore violate TERefinement.

EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, RootNode, MaxBudget, MaxWeight

Cost(n) == 2
TargetChildren(n) == IF n = RootNode THEN Nodes \ {RootNode} ELSE {}

VARIABLES edges, adjacency,
          b_capacity, b_allocated, b_reserved, b_pending,
          queue, visited, accepted

vars == <<edges, adjacency, b_capacity, b_allocated, b_reserved, b_pending,
          queue, visited, accepted>>

Graph == INSTANCE RelationshipGraph WITH Nodes <- Nodes,
                                         MaxWeight <- MaxWeight,
                                         AllowSelfLoops <- FALSE,
                                         edges <- edges,
                                         adjacency <- adjacency
Bgt == INSTANCE Budget WITH Capacity <- MaxBudget,
                            capacity <- b_capacity,
                            allocated <- b_allocated,
                            reserved <- b_reserved,
                            pending_eviction <- b_pending

GraphAdjacency == Graph!AdjacencyConsistency
GraphNoSelfLoops == Graph!NoSelfLoops
BudgetSafety == Bgt!SafetyInvariant

FullTopology == \A n \in Nodes : adjacency[n] = TargetChildren(n)

TypeInvariant ==
    /\ edges \subseteq (Nodes \X Nodes \X (0..MaxWeight))
    /\ adjacency \in [Nodes -> SUBSET Nodes]
    /\ b_capacity = MaxBudget
    /\ b_allocated \in 0..MaxBudget
    /\ b_reserved = 0
    /\ b_pending = 0
    /\ queue \subseteq Nodes
    /\ visited \subseteq Nodes
    /\ accepted \subseteq Nodes

Init ==
    /\ edges = {}
    /\ adjacency = [n \in Nodes |-> {}]
    /\ b_capacity = MaxBudget
    /\ b_allocated = 0
    /\ b_reserved = 0
    /\ b_pending = 0
    /\ queue = {RootNode}
    /\ visited = {}
    /\ accepted = {}

LoadEdge(src, dst, w) ==
    /\ visited = {}
    /\ src /= dst
    /\ dst \notin adjacency[src]
    /\ edges' = edges \cup {<<src, dst, w>>}
    /\ adjacency' = [adjacency EXCEPT ![src] = @ \cup {dst}]
    /\ UNCHANGED <<b_capacity, b_allocated, b_reserved, b_pending,
                   queue, visited, accepted>>

\* BROKEN: the accept branch omits the Budget deduct.
VisitNode(n) ==
    /\ FullTopology
    /\ n \in queue
    /\ n \notin visited
    /\ visited' = visited \cup {n}
    /\ IF b_allocated + b_reserved + b_pending + Cost(n) <= b_capacity
       THEN /\ accepted' = accepted \cup {n}
            /\ b_allocated' = b_allocated
            /\ queue' = (queue \ {n}) \cup adjacency[n]
       ELSE /\ accepted' = accepted
            /\ b_allocated' = b_allocated
            /\ queue' = queue \ {n}
    /\ UNCHANGED <<edges, adjacency, b_capacity, b_reserved, b_pending>>

Skip(n) ==
    /\ FullTopology
    /\ n \in queue
    /\ queue' = queue \ {n}
    /\ UNCHANGED <<edges, adjacency, b_capacity, b_allocated, b_reserved,
                   b_pending, visited, accepted>>

Terminate ==
    /\ queue = {}
    /\ UNCHANGED vars

Next ==
    \/ \E s, d \in Nodes, w \in 0..MaxWeight : LoadEdge(s, d, w)
    \/ \E n \in Nodes : VisitNode(n)
    \/ \E n \in Nodes : Skip(n)
    \/ Terminate

Spec == Init /\ [][Next]_vars

TE == INSTANCE TraversalEngine WITH
        budget_remaining <- b_capacity - b_allocated,
        visited          <- visited,
        accepted         <- accepted,
        queue            <- queue,
        Nodes            <- Nodes,
        RootNode         <- RootNode,
        MaxBudget        <- MaxBudget

TERefinement == TE!Spec

\* Spec => TERefinement is checked as PROPERTY TERefinement by this
\* module's .cfg and is EXPECTED TO VIOLATE (that is the control's
\* purpose).
====
