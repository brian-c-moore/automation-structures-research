---- MODULE FederatedBudgetFromBudgets ----
\* A FederatedBudget represented by one master Budget and one Budget per
\* sub-pool. The mapped sub-pool capacity is the derived ledger view
\* sub_alloc[n] + sub_res[n]; no additional glue state is held.
\*
\* CarveSubPool atomically allocates from the master and reserves the same
\* amount in one sub-pool. ConsumeFromSubPool transfers reserve to allocation.
\* ReleaseFromSubPool transfers allocation back to reserve. These atomic
\* paired operations are the construction's commit boundary.

EXTENDS Naturals, FiniteSets

CONSTANTS SubPoolNames, MasterCapacity

\* Master Budget component state + subpool Budget component state (one
\* Budget per name, held as functions over SubPoolNames). No glue variables.
VARIABLES m_capacity, m_allocated, m_reserved, m_pending,
          sub_alloc, sub_res, sub_pend

vars == <<m_capacity, m_allocated, m_reserved, m_pending,
          sub_alloc, sub_res, sub_pend>>

\* Each sub-pool Budget uses MasterCapacity as a common sound ceiling; its
\* effective delegated capacity is the allocated-plus-reserved ledger view.
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

\* Master!TryAllocate(a) success branch + Sub(name)!Reserve(a), atomic.
\* Both primitives' own guards are written out.
CarveSubPool(name, a) ==
    /\ m_allocated + m_reserved + m_pending + a <= m_capacity
    /\ sub_alloc[name] + sub_res[name] + sub_pend[name] + a <= MasterCapacity
    /\ m_allocated' = m_allocated + a
    /\ sub_res' = [sub_res EXCEPT ![name] = @ + a]
    /\ UNCHANGED <<m_capacity, m_reserved, m_pending, sub_alloc, sub_pend>>

\* Sub(name)!CommitReservation(a): reserved capacity becomes consumption;
\* the capacity view allocated+reserved is conserved.
ConsumeFromSubPool(name, a) ==
    /\ a <= sub_res[name]
    /\ sub_alloc' = [sub_alloc EXCEPT ![name] = @ + a]
    /\ sub_res' = [sub_res EXCEPT ![name] = @ - a]
    /\ UNCHANGED <<m_capacity, m_allocated, m_reserved, m_pending, sub_pend>>

\* Sub(name)!MarkEviction(a) + CompleteEviction(a) + Reserve(a), fused
\* atomically: consumption returns to reserve; the capacity view is
\* conserved. The second conjunct is the re-Reserve guard at the net state.
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

\* Refinement mapping to FederatedBudget. sub_capacities is derived from each
\* sub-pool's allocated and reserved Budget fields.
MapSubCapacities == [n \in SubPoolNames |-> sub_alloc[n] + sub_res[n]]

FB == INSTANCE FederatedBudget WITH
        master_allocated <- m_allocated,
        sub_capacities   <- MapSubCapacities,
        sub_allocated    <- sub_alloc,
        SubPoolNames     <- SubPoolNames,
        MasterCapacity   <- MasterCapacity

\* Every construction behavior must map to a FederatedBudget behavior.
FBRefinement == FB!Spec

\* The configuration checks this property at its finite bounds; the proof
\* module establishes Spec => FBRefinement parametrically.
====
