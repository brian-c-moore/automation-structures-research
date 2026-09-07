---- MODULE ALKClaimInstantiationWitness ----
EXTENDS ALKClaimFrameData

VARIABLES budget_capacity, budget_allocated, budget_reserved,
          budget_pending_eviction,
          sequential_pc, sequential_value, sequential_active,
          sequential_history

vars ==
    <<budget_capacity, budget_allocated, budget_reserved,
      budget_pending_eviction,
      sequential_pc, sequential_value, sequential_active,
      sequential_history>>

budgetVars ==
    <<budget_capacity, budget_allocated, budget_reserved,
      budget_pending_eviction>>

sequentialVars ==
    <<sequential_pc, sequential_value, sequential_active,
      sequential_history>>

BudgetContract == INSTANCE Budget_Proof WITH
    Capacity <- 2,
    capacity <- budget_capacity,
    allocated <- budget_allocated,
    reserved <- budget_reserved,
    pending_eviction <- budget_pending_eviction

SequentialContract == INSTANCE Sequential_Proof WITH
    Steps <- 2,
    ValueDomain <- {0, 1},
    pc <- sequential_pc,
    value <- sequential_value,
    active <- sequential_active,
    history <- sequential_history

SelectedPredicateHolds ==
    [clause \in SelectedClauseOccurrences |->
        CASE clause = "Budget!SafetyInvariant" ->
               BudgetContract!SafetyInvariant
          [] clause = "Sequential!TypeInvariant" ->
               SequentialContract!TypeInvariant
          [] clause = "Sequential!HistoryPositionAgreement" ->
               SequentialContract!HistoryPositionAgreement
          [] OTHER -> FALSE]

BudgetTypeHolds == BudgetContract!TypeInvariant
SequentialTypeHolds == SequentialContract!TypeInvariant

SelectedCatalogBindingHeld ==
    /\ SelectedStructureSchemas \subseteq RegistryObligationSchemaNames
    /\ SelectedExecutionSchemas \subseteq RegistryObligationSchemaNames
    /\ SelectedStructureSchemas \cap SelectedExecutionSchemas = {}
    /\ \A schema \in SelectedStructureSchemas :
          RegistrySchemaCarrier[schema] \in RegistryStructureNames
    /\ \A schema \in SelectedExecutionSchemas :
          RegistrySchemaCarrier[schema] \in RegistryExecutionModalityNames
    /\ \A schema \in SelectedSchemas :
          /\ RegistrySchemaCatalogMode[schema] =
               FrameOfSchema[schema].mode
          /\ RegistrySchemaClauses[schema] # {}
    /\ SelectedStructureClauseOccurrences = {"Budget!SafetyInvariant"}
    /\ SelectedExecutionClauseOccurrences =
         {"Sequential!TypeInvariant",
          "Sequential!HistoryPositionAgreement"}
    /\ RegistryClausePredicatePathOf["Budget!SafetyInvariant"] =
         "formal/structures/Budget/Budget.tla"
    /\ RegistryClausePredicateOperatorOf["Budget!SafetyInvariant"] =
         "SafetyInvariant"
    /\ RegistryClausePredicatePathOf["Sequential!TypeInvariant"] =
         "formal/execution/carriers/Sequential.tla"
    /\ RegistryClausePredicateOperatorOf["Sequential!TypeInvariant"] =
         "TypeInvariant"
    /\ RegistryClausePredicatePathOf[
           "Sequential!HistoryPositionAgreement"] =
         "formal/execution/carriers/Sequential.tla"
    /\ RegistryClausePredicateOperatorOf[
           "Sequential!HistoryPositionAgreement"] =
         "HistoryPositionAgreement"
    /\ RegistryClauseStatusOf["Budget!SafetyInvariant"] = "primary"
    /\ RegistryClauseStatusOf["Sequential!TypeInvariant"] = "support"
    /\ RegistryClauseStatusOf[
           "Sequential!HistoryPositionAgreement"] = "contributing"
    /\ RegistryClauseAssumptionSetOf["Budget!SafetyInvariant"] = "A-BUD"
    /\ RegistryClauseAssumptionSetOf["Sequential!TypeInvariant"] = "A-SEQ"
    /\ RegistryClauseAssumptionSetOf[
           "Sequential!HistoryPositionAgreement"] = "A-SEQ"

CompleteClaimFramesHeld ==
    /\ ClaimFramesTyped(
           Frames, Subjects, ObligationSchemas, Modes, Scopes,
           ObservationBoundaries, AuthorityBoundaries,
           Claimants, FailureModels, Abstractions, LifecyclePhases)
    /\ DOMAIN FrameOfSchema = SelectedSchemas
    /\ {FrameOfSchema[schema] : schema \in SelectedSchemas} = Frames
    /\ \A frame \in Frames :
          /\ frame.propertyForm = "safety"
          /\ DecisiveBehaviorOfSchema[frame.obligation] # {}
          /\ DecisiveBehaviorOfSchema[frame.obligation] =
               AuthorityBoundaryBehaviorOfFrame[frame]
          /\ FailureConditionsOfFrame[frame] # {}
          /\ ObservedStateOfFrame[frame] # {}

SelectedPredicatesHold ==
    /\ BudgetContract!SafetyInvariant
    /\ SequentialContract!TypeInvariant
    /\ SequentialContract!HistoryPositionAgreement

FramePredicateHolds ==
    [frame \in Frames |->
        IF frame = BudgetFrame
          THEN BudgetContract!SafetyInvariant
        ELSE /\ SequentialContract!TypeInvariant
             /\ SequentialContract!HistoryPositionAgreement]

FrameViolation == [frame \in Frames |-> ~FramePredicateHolds[frame]]

ObservedValuesOfFrame ==
    [frame \in Frames |->
        IF frame = BudgetFrame THEN budgetVars ELSE sequentialVars]

SelectedClauseEvaluationHeld ==
    \A clause \in SelectedClauseOccurrences : SelectedPredicateHolds[clause]

ClaimInstantiationHeld ==
    /\ SelectedCatalogBindingHeld
    /\ CompleteClaimFramesHeld
    /\ SelectedPredicatesHold
    /\ SelectedClauseEvaluationHeld
    /\ \A frame \in Frames : FramePredicateHolds[frame]

Init ==
    /\ BudgetContract!Init
    /\ SequentialContract!Init

BudgetStep ==
    /\ BudgetContract!Next
    /\ UNCHANGED sequentialVars

SequentialStep ==
    /\ SequentialContract!Next
    /\ UNCHANGED budgetVars

Next == BudgetStep \/ SequentialStep

BoundBudgetAction(behavior) ==
    CASE behavior = "budget-try-allocate" ->
           \E amount \in 1..budget_capacity : BudgetContract!TryAllocate(amount)
      [] behavior = "budget-reserve" ->
           \E amount \in 1..budget_capacity : BudgetContract!Reserve(amount)
      [] behavior = "budget-commit-reservation" ->
           \E amount \in 1..budget_reserved : BudgetContract!CommitReservation(amount)
      [] behavior = "budget-release" ->
           \E amount \in 1..budget_allocated : BudgetContract!Release(amount)
      [] behavior = "budget-mark-eviction" ->
           \E amount \in 1..budget_allocated : BudgetContract!MarkEviction(amount)
      [] behavior = "budget-complete-eviction" ->
           \E amount \in 1..budget_pending_eviction : BudgetContract!CompleteEviction(amount)
      [] OTHER -> FALSE

BoundSequentialAction(behavior) ==
    CASE behavior = "sequential-begin" -> SequentialContract!BeginStep
      [] behavior = "sequential-complete" -> SequentialContract!CompleteStep
      [] behavior = "sequential-done" -> SequentialContract!DoneStuttering
      [] OTHER -> FALSE

BoundBehaviorStep(behavior) ==
    IF behavior \in BudgetBehaviors
      THEN /\ BoundBudgetAction(behavior)
           /\ UNCHANGED sequentialVars
      ELSE /\ behavior \in SequentialBehaviors \cup {"sequential-done"}
           /\ BoundSequentialAction(behavior)
           /\ UNCHANGED budgetVars

BoundNext == \E behavior \in CatalogBehaviors : BoundBehaviorStep(behavior)

Spec == Init /\ [][Next]_vars

====
