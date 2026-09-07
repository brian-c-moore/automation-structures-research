---- MODULE RelationshipGraph ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, MaxWeight, AllowSelfLoops

ASSUME LoopPolicyType == AllowSelfLoops \in BOOLEAN

VARIABLES edges, adjacency

vars == <<edges, adjacency>>

TypeInvariant ==
    /\ edges \subseteq (Nodes \X Nodes \X (0..MaxWeight))
    /\ adjacency \in [Nodes -> SUBSET Nodes]

\* Adjacency is an independent view of the edge set. AddEdge and RemoveEdge
\* update both views atomically; the adjacency control omits one paired update.
AdjacencyConsistency ==
    \A src \in Nodes : adjacency[src] =
        {dst \in Nodes : \E w \in 0..MaxWeight : <<src, dst, w>> \in edges}

\* Irreflexivity is one selectable graph policy, not an intrinsic graph duty.
NoSelfLoops ==
    \A n \in Nodes : n \notin adjacency[n]

SelectedLoopPolicy == AllowSelfLoops \/ NoSelfLoops

Init ==
    /\ edges = {}
    /\ adjacency = [n \in Nodes |-> {}]

AddEdge(src, dst, weight) ==
    /\ AllowSelfLoops \/ src /= dst
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

\* The proof establishes projection integrity for both loop policies and
\* irreflexivity only when the irreflexive profile is selected.
====
