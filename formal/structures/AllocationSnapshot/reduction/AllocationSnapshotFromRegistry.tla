---- MODULE AllocationSnapshotFromRegistry ----
\* Construction of AllocationSnapshot from an insert-only ResourceRegistry
\* fragment and Budget allocation. The refinement mapping is:
\*     accepted         = the registered-key projection,
\*     total_cost       = allocated,
\*     budget_remaining = capacity - allocated.
\* The construction adds no held glue state; each mapped value is a projection
\* over component state. Its explicit composition assumption is that registry
\* insertion and Budget allocation commit atomically in AcceptNode.

EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, BudgetCapacity

CostValues == 1..BudgetCapacity

\* ResourceRegistry component state (entries) + Budget component state
\* (capacity/allocated/reserved/pending_eviction). No glue variables.
VARIABLES entries, capacity, allocated, reserved, pending_eviction

vars == <<entries, capacity, allocated, reserved, pending_eviction>>

\* Component instances and their carried safety invariants.
RR == INSTANCE ResourceRegistry WITH Keys <- Nodes, Values <- CostValues
Budget == INSTANCE Budget WITH Capacity <- BudgetCapacity

RegistryUnique == RR!UniqueMapping     \* every key maps to at most one value
BudgetSafety == Budget!SafetyInvariant \* allocated+reserved+pending_eviction <= capacity

TypeInvariant ==
    /\ entries \subseteq (Nodes \X CostValues)
    /\ capacity = BudgetCapacity
    /\ allocated \in 0..BudgetCapacity
    /\ reserved = 0
    /\ pending_eviction = 0

Init ==
    /\ entries = {}
    /\ capacity = BudgetCapacity
    /\ allocated = 0
    /\ reserved = 0
    /\ pending_eviction = 0

\* AcceptNode combines the fresh-key branch of RR!Register with the successful
\* allocation branch of Budget!TryAllocate in one transition.
AcceptNode(n, c) ==
    /\ ~\E v \in CostValues : <<n, v>> \in entries
    /\ allocated + reserved + pending_eviction + c <= capacity
    /\ entries' = {e \in entries : e[1] /= n} \cup {<<n, c>>}
    /\ allocated' = allocated + c
    /\ UNCHANGED <<capacity, reserved, pending_eviction>>

Next ==
    \E n \in Nodes, c \in CostValues : AcceptNode(n, c)

Spec == Init /\ [][Next]_vars

\* Refinement mapping to AllocationSnapshot. All three mapped values are
\* projections over component state.
MapAccepted == {k \in Nodes : \E v \in CostValues : <<k, v>> \in entries}

AS == INSTANCE AllocationSnapshot WITH
        accepted         <- MapAccepted,
        total_cost       <- allocated,
        budget_remaining <- capacity - allocated,
        Nodes            <- Nodes,
        BudgetCapacity   <- BudgetCapacity

\* Every behavior of the composition must map to an AllocationSnapshot
\* behavior.
ASRefinement == AS!Spec

\* Spec => ASRefinement: TLC-checked as PROPERTY ASRefinement (this module's
\* .cfg, bounded); proved unbounded/parametric as Refinement in
\* AllocationSnapshotFromRegistry_Proof.tla.
====
