-------------------- MODULE AllocationSnapshotDecomposed --------------------
(* Decomposition of allocation snapshot: allows post-hoc force insertions.
   AcceptNode is budget-checked but ForceInsert bypasses the check, causing
   total_cost + budget_remaining to exceed OriginalBudget.
   TLC finds BudgetConsistency violated.

   This module is not AllocationSnapshot-minus-one-mechanism, and it is not a
   check-act split: both actions are single-step and `pc` never leaves
   "idle".  It adds an unchecked post-hoc writer, and it diverges from the
   canonical module in three further ways: the `accepted` set and `Nodes` are
   gone (so ForceInsert inserts no node, it adds cost only, and the model's
   state space is infinite but for the depth-2 violation), the per-call cost
   parameter is frozen to the constant NodeCost, and the budget bound is
   re-valued relative to the canonical .cfg's.  BudgetConsistency fires in
   one ForceInsert step for the stated reason (cost added with no deduction),
   a step no canonical action can produce.

   The check-act split witness for this entry is
   irreducibility/AllocationSnapshotAcceptDecomposed.                       *)
EXTENDS Naturals, FiniteSets

CONSTANT OriginalBudget   \* e.g. 4
CONSTANT NodeCost         \* e.g. 2
CONSTANT NULL

VARIABLE budget_remaining, total_cost, pc

vars == <<budget_remaining, total_cost, pc>>

Init ==
    /\ budget_remaining = OriginalBudget
    /\ total_cost = 0
    /\ pc = "idle"

(* Checked accept: verifies budget before allocating *)
AcceptNode ==
    /\ pc = "idle"
    /\ budget_remaining >= NodeCost
    /\ budget_remaining' = budget_remaining - NodeCost
    /\ total_cost' = total_cost + NodeCost
    /\ pc' = "idle"

(* Force insert: adds cost without checking budget, doesn't deduct *)
ForceInsert ==
    /\ pc = "idle"
    /\ total_cost' = total_cost + NodeCost
    /\ UNCHANGED budget_remaining     \* no deduction
    /\ pc' = "idle"

Next ==
    \/ AcceptNode
    \/ ForceInsert

(* Total cost plus remaining budget should never exceed original *)
BudgetConsistency == total_cost + budget_remaining <= OriginalBudget

Spec == Init /\ [][Next]_vars
=============================================================================
