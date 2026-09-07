---- MODULE EquivalenceClassImplRefinesSpec_NEG ----
(***************************************************************************)
(* Isolated atomicity fault: count a successful operation without merging  *)
(* two classes. All structural representative and rank invariants remain   *)
(* true; no canonical Union step has this observation.                      *)
(***************************************************************************)
\* EXPECT: VIOLATION
EXTENDS EquivalenceClassImplRefinesSpec

AdjacentInvariant == ImplInvariant
FaultCountOnly ==
    /\ AdjacentInvariant
    /\ ops_done < max_ops
    /\ ops_done' = ops_done + 1
    /\ UNCHANGED <<num_elements, max_ops, parent, rnk, size, max_rank>>
    /\ AdjacentInvariant'

FaultNext == FaultCountOnly
    \/ (\E a \in ElementSet, b \in ElementSet : ImplUnion(a, b))
    \/ ImplReadOrReject
FaultRefinement == E!Spec
====
