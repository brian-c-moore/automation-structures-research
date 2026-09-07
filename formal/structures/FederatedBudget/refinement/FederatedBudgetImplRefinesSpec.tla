---- MODULE FederatedBudgetImplRefinesSpec ----
(***************************************************************************)
(* Contract transcription for FederatedBudget. The two Vec fields map      *)
(* indexwise to functions over pool indices. master_capacity and pool      *)
(* count are immutable. Invalid names, zero amounts, and failed guards      *)
(* stutter under the observation map.                                      *)
(***************************************************************************)
\* EXPECT: OK
EXTENDS Naturals, FiniteSets

CONSTANTS MasterCapacity, NumPools
ASSUME MasterType == MasterCapacity \in Nat /\ MasterCapacity >= 1
ASSUME PoolCountType == NumPools \in Nat /\ NumPools >= 2
Pools == 0..(NumPools - 1)

VARIABLES master_capacity, num_pools,
          master_allocated, sub_capacities, sub_allocated
vars == <<master_capacity, num_pools,
          master_allocated, sub_capacities, sub_allocated>>

F == INSTANCE FederatedBudget WITH
        SubPoolNames <- Pools,
        MasterCapacity <- MasterCapacity,
        master_allocated <- master_allocated,
        sub_capacities <- sub_capacities,
        sub_allocated <- sub_allocated

ImplInvariant ==
    /\ master_capacity = MasterCapacity
    /\ num_pools = NumPools
    /\ F!TypeInvariant
    /\ F!MasterCapacityBound
    /\ F!SubPoolCapacityBound
    /\ F!CapacityConservation

Init ==
    /\ master_capacity = MasterCapacity
    /\ num_pools = NumPools
    /\ master_allocated = 0
    /\ sub_capacities = [n \in Pools |-> 0]
    /\ sub_allocated = [n \in Pools |-> 0]
    /\ ImplInvariant

ImplAllocateSubPool(name, amount) ==
    /\ ImplInvariant
    /\ name \in Pools
    /\ amount \in 1..MasterCapacity
    /\ IF master_allocated + amount <= MasterCapacity
       THEN /\ master_allocated' = master_allocated + amount
            /\ sub_capacities' = [sub_capacities EXCEPT ![name] = @ + amount]
            /\ UNCHANGED sub_allocated
       ELSE UNCHANGED <<master_allocated, sub_capacities, sub_allocated>>
    /\ UNCHANGED <<master_capacity, num_pools>>
    /\ ImplInvariant'

ImplAllocateFromSubPool(name, amount) ==
    /\ ImplInvariant
    /\ name \in Pools
    /\ amount \in 1..MasterCapacity
    /\ IF sub_allocated[name] + amount <= sub_capacities[name]
       THEN /\ sub_allocated' = [sub_allocated EXCEPT ![name] = @ + amount]
            /\ UNCHANGED <<master_allocated, sub_capacities>>
       ELSE UNCHANGED <<master_allocated, sub_capacities, sub_allocated>>
    /\ UNCHANGED <<master_capacity, num_pools>>
    /\ ImplInvariant'

ImplReleaseFromSubPool(name, amount) ==
    /\ ImplInvariant
    /\ name \in Pools
    /\ amount \in 1..MasterCapacity
    /\ amount <= sub_allocated[name]
    /\ sub_allocated' = [sub_allocated EXCEPT ![name] = @ - amount]
    /\ UNCHANGED <<master_capacity, num_pools,
                    master_allocated, sub_capacities>>
    /\ ImplInvariant'

ImplReadOrReject == UNCHANGED vars
ImplNext ==
    \/ \E n \in Pools, a \in 1..MasterCapacity : ImplAllocateSubPool(n, a)
    \/ \E n \in Pools, a \in 1..MasterCapacity : ImplAllocateFromSubPool(n, a)
    \/ \E n \in Pools, a \in 1..MasterCapacity : ImplReleaseFromSubPool(n, a)
    \/ ImplReadOrReject
Spec == Init /\ [][ImplNext]_vars

Refinement == F!Spec
====
