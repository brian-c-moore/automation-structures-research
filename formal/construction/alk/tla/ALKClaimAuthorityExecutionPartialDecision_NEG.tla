---- MODULE ALKClaimAuthorityExecutionPartialDecision_NEG ----
EXTENDS ALKClaimAuthorityExecutionWitness

PartialDecisionBypass ==
    /\ authorityMode = "protocol"
    /\ BoundBehaviorStep("budget-try-allocate")
    /\ budgetVars' # budgetVars
    /\ RecordExecution("alk-protocol", {"budget-authority"}, "budget-try-allocate", "commit")

NegativeControlSpec ==
    ExecutionInit /\ [][PartialDecisionBypass \/ ExecutionNext]_executionVars

NegativeControlExpected == CommitAuthorizationHeld

====
