---- MODULE BacktrackingTraversalImplRefinesSpec_NEG ----
(***************************************************************************)
(* Isolated visit fault: from leaf <<1>>, record the other valid leaf      *)
(* <<2>>. All four adjacent invariants remain true, but Visit action        *)
(* correspondence fails.                                                   *)
(***************************************************************************)
\* EXPECT: VIOLATION
EXTENDS BacktrackingTraversalImplRefinesSpec

AdjacentInvariant == ImplInvariant
FaultVisit ==
    /\ AdjacentInvariant
    /\ max_depth = 1
    /\ branch_factor = 2
    /\ path = <<1>>
    /\ <<2>> \notin visited
    /\ visited' = visited \cup {<<2>>}
    /\ UNCHANGED <<branch_factor, max_depth, init_aux, path, aux, ledger>>
    /\ AdjacentInvariant'

FaultNext ==
    \/ \E c \in 1..BranchFactor, d \in DeltaSet : ImplDescend(c, d)
    \/ FaultVisit
    \/ ImplAscend
    \/ ImplReadOrReject
FaultRefinement == B!Spec
====
