---- MODULE RelationshipGraph_NEG_AdjacencyConsistency ----
\* Negative control for AdjacencyConsistency.
\* AddEdge inserts the weighted edge but leaves the independent adjacency view
\* unchanged. The isolated configuration must report AdjacencyConsistency
\* violated; success would mean the paired-view fault was not exercised.

EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, MaxWeight, AllowSelfLoops

ASSUME LoopPolicyType == AllowSelfLoops \in BOOLEAN

VARIABLES edges, adjacency

vars == <<edges, adjacency>>

TypeInvariant ==
    /\ edges \subseteq (Nodes \X Nodes \X (0..MaxWeight))
    /\ adjacency \in [Nodes -> SUBSET Nodes]

AdjacencyConsistency ==
    \A src \in Nodes : adjacency[src] =
        {dst \in Nodes : \E w \in 0..MaxWeight : <<src, dst, w>> \in edges}

NoSelfLoops ==
    \A n \in Nodes : n \notin adjacency[n]

Init ==
    /\ edges = {}
    /\ adjacency = [n \in Nodes |-> {}]

AddEdge(src, dst, weight) ==
    /\ AllowSelfLoops \/ src /= dst
\* Fault: omit the adjacency update paired with the edge insertion.
    /\ edges' = edges \cup {<<src, dst, weight>>}
    /\ UNCHANGED adjacency

RemoveEdge(src, dst) ==
    /\ \E w \in 0..MaxWeight : <<src, dst, w>> \in edges
    /\ edges' = {e \in edges : ~(e[1] = src /\ e[2] = dst)}
    /\ adjacency' = [adjacency EXCEPT ![src] = @ \ {dst}]

Next ==
    \/ \E s, d \in Nodes, w \in 0..MaxWeight : AddEdge(s, d, w)
    \/ \E s, d \in Nodes : RemoveEdge(s, d)

Spec == Init /\ [][Next]_vars

====
