---- MODULE AllocationSnapshotFromRegistry_NEG ----
\* Negative control for ASRefinement in AllocationSnapshotFromRegistry.
\* AcceptNode registers a fresh node without deducting its cost. The component
\* invariants still hold, but the mapped accepted set changes while mapped
\* total_cost and budget_remaining stutter. This is neither an
\* AS!AcceptNode step nor a mapped stutter, so ASRefinement is
\* expected to be violated.

EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, BudgetCapacity

CostValues == 1..BudgetCapacity

VARIABLES entries, capacity, allocated, reserved, pending_eviction

vars == <<entries, capacity, allocated, reserved, pending_eviction>>

RR == INSTANCE ResourceRegistry WITH Keys <- Nodes, Values <- CostValues
Budget == INSTANCE Budget WITH Capacity <- BudgetCapacity

RegistryUnique == RR!UniqueMapping
BudgetSafety == Budget!SafetyInvariant

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

\* Control fault: register without the matching Budget allocation.
AcceptNode(n, c) ==
    /\ ~\E v \in CostValues : <<n, v>> \in entries
    /\ allocated + reserved + pending_eviction + c <= capacity
    /\ entries' = {e \in entries : e[1] /= n} \cup {<<n, c>>}
    /\ UNCHANGED <<capacity, allocated, reserved, pending_eviction>>

Next ==
    \E n \in Nodes, c \in CostValues : AcceptNode(n, c)

Spec == Init /\ [][Next]_vars

MapAccepted == {k \in Nodes : \E v \in CostValues : <<k, v>> \in entries}

AS == INSTANCE AllocationSnapshot WITH
        accepted         <- MapAccepted,
        total_cost       <- allocated,
        budget_remaining <- capacity - allocated,
        Nodes            <- Nodes,
        BudgetCapacity   <- BudgetCapacity

ASRefinement == AS!Spec

\* The configuration checks ASRefinement and expects the control fault above
\* to produce a violation.
====
