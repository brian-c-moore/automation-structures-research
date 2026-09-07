---- MODULE TraversalEngineFromGraphBudget ----
\* Refinement construction for TraversalEngine from RelationshipGraph,
\* Budget, and admitted glue.
\*
\* Glue profile:
\*   - budget_remaining = capacity - allocated : CF-001 Projection
\*   - visited                               : CF-004 Marker
\*   - accepted                              : CF-003 Accumulator
\*   - queue                                 : Buffer
\*
\* Queue is held state rather than a projection: Skip can remove a queued node
\* without visiting it, so equal component, marker, and accumulator state can
\* still have different frontiers.
\*
\* Visit and budget deduction commit atomically. Graph edges are loaded before
\* walking begins; those loading steps map to TraversalEngine stutters, and a
\* walk begins only after the target topology has been loaded.

EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, RootNode, MaxBudget, MaxWeight

\* The target's own model content, mirrored: per-node cost and the fixed
\* star topology the walk must realize (TraversalEngine hardcodes these as
\* definitions; here the topology lives in the RelationshipGraph and the
\* walk is gated on having built exactly it).
Cost(n) == 2
TargetChildren(n) == IF n = RootNode THEN Nodes \ {RootNode} ELSE {}

\* RelationshipGraph component state (edges, adjacency) + Budget component
\* state (b_*) + the walk glue (queue, visited, accepted -- see the glue
\* profile above).
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

\* Component invariants exposed by the instantiated graph and budget modules.
GraphAdjacency == Graph!AdjacencyConsistency
GraphNoSelfLoops == Graph!NoSelfLoops
BudgetSafety == Bgt!SafetyInvariant

\* The walk gate: the graph holds exactly the target topology.
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

\* Graph!AddEdge(src, dst, w), insert-only usage, before the walk begins.
\* Maps to a TraversalEngine stutter (no mapped variable moves).
LoadEdge(src, dst, w) ==
    /\ visited = {}
    /\ src /= dst
    /\ dst \notin adjacency[src]
    /\ edges' = edges \cup {<<src, dst, w>>}
    /\ adjacency' = [adjacency EXCEPT ![src] = @ \cup {dst}]
    /\ UNCHANGED <<b_capacity, b_allocated, b_reserved, b_pending,
                   queue, visited, accepted>>

\* TraversalEngine!VisitNode(n): the accept branch is Bgt!TryAllocate(Cost)
\* fused with the visit and the frontier expansion over the graph's
\* adjacency (which the FullTopology gate makes equal the target's
\* NodeChildren); the reject branch visits without charging.
VisitNode(n) ==
    /\ FullTopology
    /\ n \in queue
    /\ n \notin visited
    /\ visited' = visited \cup {n}
    /\ IF b_allocated + b_reserved + b_pending + Cost(n) <= b_capacity
       THEN /\ accepted' = accepted \cup {n}
            /\ b_allocated' = b_allocated + Cost(n)
            /\ queue' = (queue \ {n}) \cup adjacency[n]
       ELSE /\ accepted' = accepted
            /\ b_allocated' = b_allocated
            /\ queue' = queue \ {n}
    /\ UNCHANGED <<edges, adjacency, b_capacity, b_reserved, b_pending>>

\* TraversalEngine!Skip(n): remove a queued node without visiting it.
Skip(n) ==
    /\ FullTopology
    /\ n \in queue
    /\ queue' = queue \ {n}
    /\ UNCHANGED <<edges, adjacency, b_capacity, b_allocated, b_reserved,
                   b_pending, visited, accepted>>

\* TraversalEngine!Terminate: the walk is exhausted.
Terminate ==
    /\ queue = {}
    /\ UNCHANGED vars

Next ==
    \/ \E s, d \in Nodes, w \in 0..MaxWeight : LoadEdge(s, d, w)
    \/ \E n \in Nodes : VisitNode(n)
    \/ \E n \in Nodes : Skip(n)
    \/ Terminate

Spec == Init /\ [][Next]_vars

\* --- Refinement mapping to TraversalEngine ---
\* budget_remaining is the unallocated part of the Budget component; the
\* traversal sets and queue map identically.
TE == INSTANCE TraversalEngine WITH
        budget_remaining <- b_capacity - b_allocated,
        visited          <- visited,
        accepted         <- accepted,
        queue            <- queue,
        Nodes            <- Nodes,
        RootNode         <- RootNode,
        MaxBudget        <- MaxBudget

\* Every behaviour satisfying this property is a TraversalEngine behaviour
\* under the mapping above.
TERefinement == TE!Spec

\* The paired configuration checks Spec => TERefinement at its finite bounds.
====
