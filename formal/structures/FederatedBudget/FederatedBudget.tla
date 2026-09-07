---- MODULE FederatedBudget ----
EXTENDS Naturals, FiniteSets

CONSTANTS SubPoolNames, MasterCapacity

VARIABLES master_allocated, sub_capacities, sub_allocated

vars == <<master_allocated, sub_capacities, sub_allocated>>

TypeInvariant ==
    /\ master_allocated \in Nat
    /\ sub_capacities \in [SubPoolNames -> Nat]
    /\ sub_allocated \in [SubPoolNames -> Nat]

\* The master allocation never exceeds its declared capacity. AllocateSubPool
\* enforces the bound; the other actions leave master_allocated unchanged.
\* FederatedBudget_NEG_MasterCapacityBound removes the allocation guard.
MasterCapacityBound ==
    master_allocated <= MasterCapacity

\* Each sub-pool allocation stays within its delegated capacity.
\* AllocateFromSubPool enforces the bound; capacity delegation only raises the
\* ceiling, and release lowers the allocation. FederatedBudget_NEG_
\* SubPoolCapacityBound removes the consumption guard.
SubPoolCapacityBound ==
    \A name \in SubPoolNames : sub_allocated[name] <= sub_capacities[name]

\* Sum sub_capacities over the finite set SubPoolNames. The proof assumes
\* IsFiniteSet(SubPoolNames), which supplies a bijection from 1..SubN; natural-
\* number addition makes the resulting total independent of enumeration order.
SubN == Cardinality(SubPoolNames)

SubEnum == CHOOSE seq \in [1..SubN -> SubPoolNames] :
               \A n \in SubPoolNames : \E i \in 1..SubN : seq[i] = n

CapSum[i \in 0..SubN] ==
    IF i = 0 THEN 0 ELSE CapSum[i - 1] + sub_capacities[SubEnum[i]]

\* Delegating capacity increments master_allocated and exactly one sub-pool
\* capacity by the same amount; consumption and release leave both sides
\* unchanged. FederatedBudget_NEG_CapacityConservation omits the sub-pool
\* capacity update while retaining the master increment.
CapacityConservation ==
    master_allocated = CapSum[SubN]

Init ==
    /\ master_allocated = 0
    /\ sub_capacities = [n \in SubPoolNames |-> 0]
    /\ sub_allocated = [n \in SubPoolNames |-> 0]

AllocateSubPool(name, amount) ==
    IF master_allocated + amount <= MasterCapacity
    THEN /\ master_allocated' = master_allocated + amount
         /\ sub_capacities' = [sub_capacities EXCEPT ![name] = @ + amount]
         /\ UNCHANGED sub_allocated
    ELSE UNCHANGED vars

AllocateFromSubPool(name, amount) ==
    IF sub_allocated[name] + amount <= sub_capacities[name]
    THEN /\ sub_allocated' = [sub_allocated EXCEPT ![name] = @ + amount]
         /\ UNCHANGED <<master_allocated, sub_capacities>>
    ELSE UNCHANGED vars

ReleaseFromSubPool(name, amount) ==
    /\ amount <= sub_allocated[name]
    /\ sub_allocated' = [sub_allocated EXCEPT ![name] = @ - amount]
    /\ UNCHANGED <<master_allocated, sub_capacities>>

Next ==
    \/ \E name \in SubPoolNames, a \in 1..MasterCapacity :
        AllocateSubPool(name, a)
    \/ \E name \in SubPoolNames, a \in 1..MasterCapacity :
        AllocateFromSubPool(name, a)
    \/ \E name \in SubPoolNames, a \in 1..MasterCapacity :
        ReleaseFromSubPool(name, a)

Spec == Init /\ [][Next]_vars

\* The named safety theorems in FederatedBudget_Proof establish each conjunct
\* of Spec => [](MasterCapacityBound /\ SubPoolCapacityBound /\ CapacityConservation).
====
