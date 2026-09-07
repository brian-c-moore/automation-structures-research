---- MODULE ALKClaimAuthorityExecutionFormerOwner_NEG ----
EXTENDS ALKClaimAuthorityExecutionWitness

FormerOwnerBypass ==
    /\ authorityMode = "transfer"
    /\ BoundBehaviorStep("budget-try-allocate")
    /\ budgetVars' # budgetVars
    /\ RecordExecution("budget-authority", {"budget-authority"}, "budget-try-allocate", "commit")

NegativeControlSpec ==
    ExecutionInit /\ [][FormerOwnerBypass \/ ExecutionNext]_executionVars

NegativeControlExpected == CommitAuthorizationHeld

====
