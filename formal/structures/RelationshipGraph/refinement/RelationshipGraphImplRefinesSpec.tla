---- MODULE RelationshipGraphImplRefinesSpec ----
(***************************************************************************)
(* Contract transcription for RelationshipGraph. Both Vec fields are      *)
(* projected to sets, hiding order and duplicates while retaining weighted *)
(* edge identity and the independent adjacency view. Read guards stutter.  *)
(***************************************************************************)
\* EXPECT: OK
EXTENDS Naturals, FiniteSets

CONSTANTS NumNodes, MaxWeight
ASSUME NodeCountType == NumNodes \in Nat /\ NumNodes >= 2
ASSUME WeightType == MaxWeight \in Nat
Nodes == 0..(NumNodes - 1)

VARIABLES num_nodes, max_weight, edges, adjacency
vars == <<num_nodes, max_weight, edges, adjacency>>

G == INSTANCE RelationshipGraph WITH
        Nodes <- Nodes,
        MaxWeight <- MaxWeight,
        AllowSelfLoops <- FALSE,
        edges <- edges,
        adjacency <- adjacency

ImplInvariant ==
    /\ num_nodes = NumNodes
    /\ max_weight = MaxWeight
    /\ G!TypeInvariant
    /\ G!AdjacencyConsistency
    /\ G!SelectedLoopPolicy
    /\ G!NoSelfLoops

Init ==
    /\ num_nodes = NumNodes
    /\ max_weight = MaxWeight
    /\ edges = {}
    /\ adjacency = [n \in Nodes |-> {}]
    /\ ImplInvariant

ImplAddEdge(src, dst, weight) ==
    /\ ImplInvariant
    /\ src \in Nodes
    /\ dst \in Nodes
    /\ weight \in 0..max_weight
    /\ src /= dst
    /\ edges' = edges \cup {<<src, dst, weight>>}
    /\ adjacency' = [adjacency EXCEPT ![src] = @ \cup {dst}]
    /\ UNCHANGED <<num_nodes, max_weight>>
    /\ ImplInvariant'

ImplRemoveEdge(src, dst) ==
    /\ ImplInvariant
    /\ src \in Nodes
    /\ dst \in Nodes
    /\ \E w \in 0..max_weight : <<src, dst, w>> \in edges
    /\ edges' = {e \in edges : ~(e[1] = src /\ e[2] = dst)}
    /\ adjacency' = [adjacency EXCEPT ![src] = @ \ {dst}]
    /\ UNCHANGED <<num_nodes, max_weight>>
    /\ ImplInvariant'

ImplReadOrReject == UNCHANGED vars
ImplNext ==
    \/ \E s \in Nodes, d \in Nodes, w \in 0..MaxWeight : ImplAddEdge(s, d, w)
    \/ \E s \in Nodes, d \in Nodes : ImplRemoveEdge(s, d)
    \/ ImplReadOrReject
Spec == Init /\ [][ImplNext]_vars

Refinement == G!Spec
====
