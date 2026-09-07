---- MODULE FederatedBudgetImplRefinesSpec_NEG ----
(***************************************************************************)
(* Isolated delegation fault: move one unit of capacity between pools      *)
(* without changing the master total. All three budget invariants remain   *)
(* true; no canonical action redistributes delegated capacity this way.     *)
(***************************************************************************)
\* EXPECT: VIOLATION
EXTENDS FederatedBudgetImplRefinesSpec

AdjacentInvariant == ImplInvariant
FaultRepartition ==
    /\ AdjacentInvariant
    /\ sub_capacities[0] >= 1
    /\ sub_allocated[0] = 0
    /\ sub_capacities' =
        [sub_capacities EXCEPT ![0] = @ - 1, ![1] = @ + 1]
    /\ UNCHANGED <<master_capacity, num_pools,
                    master_allocated, sub_allocated>>
    /\ AdjacentInvariant'

FaultNext ==
    \/ \E n \in Pools, a \in 1..MasterCapacity : ImplAllocateSubPool(n, a)
    \/ FaultRepartition
    \/ ImplReadOrReject
FaultRefinement == F!Spec
====
