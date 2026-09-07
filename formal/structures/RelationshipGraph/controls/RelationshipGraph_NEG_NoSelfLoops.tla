---- MODULE RelationshipGraph_NEG_NoSelfLoops ----
\* Negative control for NoSelfLoops.
\* AddEdge admits src = dst while retaining the normal edge and adjacency
\* updates. The isolated configuration must report NoSelfLoops violated;
\* success would mean the removed admission guard was not exercised.

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

\* Fault: remove the src /= dst admission guard.
AddEdge(src, dst, weight) ==
    /\ TRUE
    /\ edges' = edges \cup {<<src, dst, weight>>}
    /\ adjacency' = [adjacency EXCEPT ![src] = @ \cup {dst}]

RemoveEdge(src, dst) ==
    /\ \E w \in 0..MaxWeight : <<src, dst, w>> \in edges
    /\ edges' = {e \in edges : ~(e[1] = src /\ e[2] = dst)}
    /\ adjacency' = [adjacency EXCEPT ![src] = @ \ {dst}]

Next ==
    \/ \E s, d \in Nodes, w \in 0..MaxWeight : AddEdge(s, d, w)
    \/ \E s, d \in Nodes : RemoveEdge(s, d)

Spec == Init /\ [][Next]_vars

====
