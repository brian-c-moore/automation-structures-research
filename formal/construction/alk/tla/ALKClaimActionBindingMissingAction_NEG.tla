---- MODULE ALKClaimActionBindingMissingAction_NEG ----
EXTENDS ALKClaimActionBindingWitness

IncompleteBehaviorInventory == CatalogBehaviors \ {"budget-release"}

NegativeControlExpected ==
    lastBehavior = "initial" \/ lastBehavior \in IncompleteBehaviorInventory

====
