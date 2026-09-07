---- MODULE ALKClaimAuthorityExecutionFalseGuarantee_NEG ----
EXTENDS ALKClaimAuthorityExecutionWitness

FalseGuarantee ==
    /\ authorityMode = "direct"
    /\ budget_allocated' = budget_capacity + 1
    /\ UNCHANGED <<budget_capacity, budget_reserved, budget_pending_eviction, sequentialVars>>
    /\ RecordExecution("budget-authority", {"budget-authority"}, "budget-try-allocate", "commit")

NegativeControlSpec ==
    ExecutionInit /\ [][FalseGuarantee \/ ExecutionNext]_executionVars

NegativeControlExpected == IssuedClaimHeld

====
