--------------------- MODULE RelationshipGraphDecomposed ---------------------
(* Decomposition of relationship graph: separates edge insertion from
   adjacency update. AddEdgeStart appends to edges and leaves adjacency
   stale; AddEdgeFinish recomputes adjacency from edges. Between the two
   steps, AdjacencyConsistency is violated: edges holds the new triple
   but adjacency has not been updated to reflect it. TLC finds the invariant
   violated at depth 2.                                                      *)
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, MaxWeight

VARIABLES edges, adjacency, pc

vars == <<edges, adjacency, pc>>

TypeInvariant ==
    /\ edges \subseteq (Nodes \X Nodes \X (0..MaxWeight))
    /\ adjacency \in [Nodes -> SUBSET Nodes]
    /\ pc \in {"idle", "edge_added"}

\* Same invariant as the primitive: adjacency reflects exactly the
\* (src, dst) projection of edges.
AdjacencyConsistency ==
    \A src \in Nodes : adjacency[src] =
        {dst \in Nodes : \E w \in 0..MaxWeight : <<src, dst, w>> \in edges}

Init ==
    /\ edges = {}
    /\ adjacency = [n \in Nodes |-> {}]
    /\ pc = "idle"

\* Phase 1 of the decomposed AddEdge: append to edges, leave adjacency stale.
AddEdgeStart ==
    /\ pc = "idle"
    /\ \E src, dst \in Nodes, w \in 0..MaxWeight :
        /\ src /= dst
        /\ <<src, dst, w>> \notin edges
        /\ edges' = edges \cup {<<src, dst, w>>}
    /\ pc' = "edge_added"
    /\ UNCHANGED adjacency

\* Phase 2 of the decomposed AddEdge: rebuild adjacency from edges.
AddEdgeFinish ==
    /\ pc = "edge_added"
    /\ adjacency' = [src \in Nodes |->
        {dst \in Nodes : \E w \in 0..MaxWeight : <<src, dst, w>> \in edges}]
    /\ pc' = "idle"
    /\ UNCHANGED edges

Next ==
    \/ AddEdgeStart
    \/ AddEdgeFinish

Spec == Init /\ [][Next]_vars

\* TLC finds a violation: after AddEdgeStart and before AddEdgeFinish,
\* AdjacencyConsistency is broken. The intermediate state where edges
\* contains an entry that adjacency does not reflect is reachable at depth 2.
=============================================================================
