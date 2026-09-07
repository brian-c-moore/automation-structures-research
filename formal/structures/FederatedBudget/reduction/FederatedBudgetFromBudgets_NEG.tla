---- MODULE FederatedBudgetFromBudgets_NEG ----
\* Refinement negative control. CarveSubPool grants sub-pool reserve without
\* charging the master Budget. The component Budget invariants still hold, but
\* the mapped step changes sub_capacities while master_allocated is unchanged,
\* so it is neither a FederatedBudget action nor a mapped stutter.

EXTENDS Naturals, FiniteSets

CONSTANTS SubPoolNames, MasterCapacity

VARIABLES m_capacity, m_allocated, m_reserved, m_pending,
          sub_alloc, sub_res, sub_pend

vars == <<m_capacity, m_allocated, m_reserved, m_pending,
          sub_alloc, sub_res, sub_pend>>

Master == INSTANCE Budget WITH Capacity <- MasterCapacity,
                               capacity <- m_capacity,
                               allocated <- m_allocated,
                               reserved <- m_reserved,
                               pending_eviction <- m_pending
Sub(n) == INSTANCE Budget WITH Capacity <- MasterCapacity,
                               capacity <- MasterCapacity,
                               allocated <- sub_alloc[n],
                               reserved <- sub_res[n],
                               pending_eviction <- sub_pend[n]

MasterBudgetSafety == Master!SafetyInvariant
SubBudgetSafety == \A n \in SubPoolNames : Sub(n)!SafetyInvariant

TypeInvariant ==
    /\ m_capacity = MasterCapacity
    /\ m_allocated \in 0..MasterCapacity
    /\ m_reserved = 0
    /\ m_pending = 0
    /\ sub_alloc \in [SubPoolNames -> Nat]
    /\ sub_res \in [SubPoolNames -> Nat]
    /\ sub_pend = [n \in SubPoolNames |-> 0]

Init ==
    /\ m_capacity = MasterCapacity
    /\ m_allocated = 0
    /\ m_reserved = 0
    /\ m_pending = 0
    /\ sub_alloc = [n \in SubPoolNames |-> 0]
    /\ sub_res = [n \in SubPoolNames |-> 0]
    /\ sub_pend = [n \in SubPoolNames |-> 0]

\* Fault: omit the master allocation update from the atomic carve.
CarveSubPool(name, a) ==
    /\ m_allocated + m_reserved + m_pending + a <= m_capacity
    /\ sub_alloc[name] + sub_res[name] + sub_pend[name] + a <= MasterCapacity
    /\ sub_res' = [sub_res EXCEPT ![name] = @ + a]
    /\ UNCHANGED <<m_capacity, m_allocated, m_reserved, m_pending,
                   sub_alloc, sub_pend>>

ConsumeFromSubPool(name, a) ==
    /\ a <= sub_res[name]
    /\ sub_alloc' = [sub_alloc EXCEPT ![name] = @ + a]
    /\ sub_res' = [sub_res EXCEPT ![name] = @ - a]
    /\ UNCHANGED <<m_capacity, m_allocated, m_reserved, m_pending, sub_pend>>

ReleaseFromSubPool(name, a) ==
    /\ a <= sub_alloc[name]
    /\ sub_alloc[name] + sub_res[name] + sub_pend[name] <= MasterCapacity
    /\ sub_alloc' = [sub_alloc EXCEPT ![name] = @ - a]
    /\ sub_res' = [sub_res EXCEPT ![name] = @ + a]
    /\ UNCHANGED <<m_capacity, m_allocated, m_reserved, m_pending, sub_pend>>

Next ==
    \/ \E name \in SubPoolNames, a \in 1..MasterCapacity :
        CarveSubPool(name, a)
    \/ \E name \in SubPoolNames, a \in 1..MasterCapacity :
        ConsumeFromSubPool(name, a)
    \/ \E name \in SubPoolNames, a \in 1..MasterCapacity :
        ReleaseFromSubPool(name, a)

Spec == Init /\ [][Next]_vars

MapSubCapacities == [n \in SubPoolNames |-> sub_alloc[n] + sub_res[n]]

FB == INSTANCE FederatedBudget WITH
        master_allocated <- m_allocated,
        sub_capacities   <- MapSubCapacities,
        sub_allocated    <- sub_alloc,
        SubPoolNames     <- SubPoolNames,
        MasterCapacity   <- MasterCapacity

FBRefinement == FB!Spec

\* The configuration must report a violation of FBRefinement.
====
