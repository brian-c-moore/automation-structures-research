---- MODULE ALKClaimActionBindingWrongFrame_NEG ----
EXTENDS ALKClaimActionBindingWitness

WrongFrameStep ==
    /\ BoundBehaviorStep("budget-try-allocate")
    /\ budgetVars' # budgetVars
    /\ RecordBehavior("sequential-begin")

NegativeControlSpec ==
    BindingInit /\ [][WrongFrameStep \/ BindingNext]_bindingVars

NegativeControlExpected == ActionFrameHeld

====
