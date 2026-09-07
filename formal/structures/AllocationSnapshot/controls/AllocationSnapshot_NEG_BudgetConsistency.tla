---- MODULE AllocationSnapshot_NEG_BudgetConsistency ----
\* Negative control for BudgetConsistency in AllocationSnapshot. AcceptNode adds
\* node_cost to total_cost but does not deduct it from budget_remaining. The
\* isolated configuration must therefore reach a BudgetConsistency violation.

EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, BudgetCapacity

VARIABLES accepted, total_cost, budget_remaining

vars == <<accepted, total_cost, budget_remaining>>

TypeInvariant ==
    /\ accepted \subseteq Nodes
    /\ total_cost \in Nat
    /\ budget_remaining \in Nat

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
\* ---- MUTATION BEGINS: omit the matching budget deduction.
    /\ total_cost' = total_cost + node_cost
    /\ UNCHANGED budget_remaining
\* ---- MUTATION ENDS.

Next ==
    \E n \in Nodes, c \in 1..BudgetCapacity : AcceptNode(n, c)

Spec == Init /\ [][Next]_vars

====
