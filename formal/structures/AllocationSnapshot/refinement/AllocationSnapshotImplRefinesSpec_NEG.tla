---- MODULE AllocationSnapshotImplRefinesSpec_NEG ----
(***************************************************************************)
(* Isolated action fault: a fresh node is published without charging it.   *)
(* TypeInvariant and BudgetConsistency remain true; AcceptNode             *)
(* correspondence is the failing seam.                                    *)
(***************************************************************************)
\* EXPECT: VIOLATION
EXTENDS AllocationSnapshotImplRefinesSpec

AdjacentInvariant == ImplInvariant
FaultAccept(n, cost) ==
    /\ AdjacentInvariant
    /\ n \in NodeSet
    /\ n \notin accepted
    /\ cost \in 1..budget_remaining
    /\ accepted' = accepted \cup {n}
    /\ UNCHANGED <<capacity, num_nodes, total_cost, budget_remaining>>
    /\ AdjacentInvariant'

FaultNext ==
    (\E n \in NodeSet, cost \in 1..Capacity : FaultAccept(n, cost))
        \/ ImplAccept(0, 1) \/ ImplReadOrReject
FaultRefinement == A!Spec
====
