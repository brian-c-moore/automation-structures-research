---- MODULE AllocationSnapshot ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, BudgetCapacity

VARIABLES accepted, total_cost, budget_remaining

vars == <<accepted, total_cost, budget_remaining>>

TypeInvariant ==
    /\ accepted \subseteq Nodes
    /\ total_cost \in Nat
    /\ budget_remaining \in Nat

\* Init fixes total_cost + budget_remaining at BudgetCapacity. AcceptNode adds
\* and subtracts the same cost, preserving that equality. The matching
\* controls/AllocationSnapshot_NEG_BudgetConsistency module changes only the
\* deduction and violates the bound on a reachable state.
BudgetConsistency ==
    total_cost + budget_remaining <= BudgetCapacity

Init ==
    /\ accepted = {}
    /\ total_cost = 0
    /\ budget_remaining = BudgetCapacity

AcceptNode(n, node_cost) ==
    /\ n \notin accepted
    /\ node_cost <= budget_remaining
    /\ accepted' = accepted \cup {n}
    /\ total_cost' = total_cost + node_cost
    /\ budget_remaining' = budget_remaining - node_cost

Next ==
    \E n \in Nodes, c \in 1..BudgetCapacity : AcceptNode(n, c)

Spec == Init /\ [][Next]_vars

\* Spec => []BudgetConsistency: proved as BudgetConsistencySafety in
\* AllocationSnapshot_Proof.tla.
====
