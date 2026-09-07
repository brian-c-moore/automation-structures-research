---- MODULE ALKClaimActionBindingWitness ----
EXTENDS ALKClaimInstantiationWitness

VARIABLES lastBehavior, priorBudget, priorSequential

bindingVars == <<vars, lastBehavior, priorBudget, priorSequential>>

BindingInit ==
    /\ Init
    /\ lastBehavior = "initial"
    /\ priorBudget = budgetVars
    /\ priorSequential = sequentialVars

RecordBehavior(behavior) ==
    /\ lastBehavior' = behavior
    /\ priorBudget' = budgetVars
    /\ priorSequential' = sequentialVars

BindingNext ==
    \E behavior \in CatalogBehaviors :
      /\ BoundBehaviorStep(behavior)
      /\ RecordBehavior(behavior)

BindingSpec == BindingInit /\ [][BindingNext]_bindingVars

ActionFrameHeld ==
    /\ lastBehavior \in CatalogBehaviors \cup {"initial"}
    /\ (lastBehavior \in BudgetBehaviors => sequentialVars = priorSequential)
    /\ (lastBehavior \in SequentialBehaviors \cup {"sequential-done"}
          => budgetVars = priorBudget)

BindingInvariant == ClaimInstantiationHeld /\ ActionFrameHeld

====
