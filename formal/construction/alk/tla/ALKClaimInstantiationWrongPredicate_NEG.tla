---- MODULE ALKClaimInstantiationWrongPredicate_NEG ----
EXTENDS ALKClaimInstantiationWitness

OverCapacityCommit ==
    /\ budget_allocated = 0
    /\ budget_reserved = 0
    /\ budget_pending_eviction = 0
    /\ budget_capacity' = budget_capacity
    /\ budget_allocated' = budget_capacity + 1
    /\ budget_reserved' = budget_reserved
    /\ budget_pending_eviction' = budget_pending_eviction
    /\ UNCHANGED sequentialVars

NegativeControlNext == Next \/ OverCapacityCommit

NegativeControlSpec == Init /\ [][NegativeControlNext]_vars

AdjacentTypingSurvives ==
    /\ BudgetTypeHolds
    /\ SequentialTypeHolds

NegativeControlExpected == ClaimInstantiationHeld

====
