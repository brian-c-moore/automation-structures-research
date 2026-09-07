---- MODULE RelationshipGraphImplRefinesSpec_NEG ----
(***************************************************************************)
(* Isolated identity fault: rewrite one edge's weight without changing the *)
(* adjacency view. Both public graph invariants remain true, but canonical  *)
(* AddEdge never removes the old weighted edge.                             *)
(***************************************************************************)
\* EXPECT: VIOLATION
EXTENDS RelationshipGraphImplRefinesSpec

AdjacentInvariant == ImplInvariant
FaultRewriteWeight ==
    /\ AdjacentInvariant
    /\ <<0, 1, 0>> \in edges
    /\ <<0, 1, 1>> \notin edges
    /\ edges' = (edges \ {<<0, 1, 0>>}) \cup {<<0, 1, 1>>}
    /\ UNCHANGED <<num_nodes, max_weight, adjacency>>
    /\ AdjacentInvariant'

FaultNext ==
    ImplAddEdge(0, 1, 0) \/ FaultRewriteWeight \/ ImplReadOrReject
FaultRefinement == G!Spec
====
