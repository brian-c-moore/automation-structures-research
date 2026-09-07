---- MODULE QualityHierarchyImplRefinesSpec_NEG ----
(***************************************************************************)
(* Isolated atomicity fault: update two isolated nodes in one transition.  *)
(* All hierarchy invariants remain true, but no canonical single-node      *)
(* SetNodeProperties action has this observation.                           *)
(***************************************************************************)
\* EXPECT: VIOLATION
EXTENDS QualityHierarchyImplRefinesSpec

AdjacentInvariant == ImplInvariant
FaultBatchSet ==
    /\ AdjacentInvariant
    /\ children[0] = {}
    /\ children[1] = {}
    /\ parent[0] = Null
    /\ parent[1] = Null
    /\ level' = [level EXCEPT ![0] = 1, ![1] = 1]
    /\ cost' = [cost EXCEPT ![0] = 1, ![1] = 1]
    /\ UNCHANGED <<num_nodes, max_level, children, parent>>
    /\ AdjacentInvariant'

FaultNext == FaultBatchSet \/ ImplReadOrReject
FaultRefinement == Q!Spec
====
