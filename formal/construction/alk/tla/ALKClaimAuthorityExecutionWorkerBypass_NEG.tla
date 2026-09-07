---- MODULE ALKClaimAuthorityExecutionWorkerBypass_NEG ----
EXTENDS ALKClaimAuthorityExecutionWitness

WorkerBypass ==
    /\ authorityMode = "work"
    /\ BoundBehaviorStep("budget-try-allocate")
    /\ budgetVars' # budgetVars
    /\ RecordExecution("budget-worker", {"budget-worker"}, "budget-try-allocate", "commit")

NegativeControlSpec ==
    ExecutionInit /\ [][WorkerBypass \/ ExecutionNext]_executionVars

NegativeControlExpected == CommitAuthorizationHeld

====
