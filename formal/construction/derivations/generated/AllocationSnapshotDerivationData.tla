---- MODULE AllocationSnapshotDerivationData ----
EXTENDS StructureDerivationSchema

\* Generated from the checked derivation record. Do not edit by hand.

ImplementationStateMap ==
    [key \in {"accepted", "total_cost", "budget_remaining"} |->
        CASE key = "accepted" -> "accepted"
          [] key = "total_cost" -> "total_cost"
          [] key = "budget_remaining" -> "budget_remaining"
          [] OTHER -> "budget_remaining"]

ObservationMap ==
    [key \in {"accepted", "total_cost", "budget_remaining"} |->
        CASE key = "accepted" -> "accepted"
          [] key = "total_cost" -> "total_cost"
          [] key = "budget_remaining" -> "budget_remaining"
          [] OTHER -> "budget_remaining"]

ActionMap ==
    [key \in {"AcceptNode"} |->
        CASE key = "AcceptNode" -> {"accept_node"}
          [] OTHER -> {"accept_node"}]

ViolationOf ==
    [key \in {"BudgetConsistency"} |->
        CASE key = "BudgetConsistency" -> "SnapshotOverspend"
          [] OTHER -> "SnapshotOverspend"]

OwnerOf ==
    [key \in {"AcceptNode"} |->
        CASE key = "AcceptNode" -> "snapshot-authority"
          [] OTHER -> "snapshot-authority"]

DelegateOf ==
    [key \in {"AcceptNode"} |->
        CASE key = "AcceptNode" -> {"snapshot-authority"}
          [] OTHER -> {"snapshot-authority"}]

AssuranceAt ==
    [key \in {"AcceptNode"} |->
        CASE key = "AcceptNode" -> "at-commit"
          [] OTHER -> "at-commit"]

WitnessPersistentObserve ==
    [key \in {"empty", "accepted", "overspent"} |->
        CASE key = "empty" -> TRUE
          [] key = "accepted" -> TRUE
          [] key = "overspent" -> FALSE
          [] OTHER -> FALSE]

WitnessRank ==
    [key \in {"empty", "accepted", "overspent"} |->
        CASE key = "empty" -> 0
          [] key = "accepted" -> 0
          [] key = "overspent" -> 0
          [] OTHER -> 0]

WitnessFairnessOwnerOf == [key \in {} |-> "unused"]

WitnessActionSteps ==
    [key \in {"AcceptNode"} |->
        CASE key = "AcceptNode" -> {<<"empty", "accepted">>}
          [] OTHER -> {<<"empty", "accepted">>}]

Derivation ==
    [structure |-> "AllocationSnapshot",
     kind |-> "named-composition",
     propertyClasses |-> {"safety"},
     stateFields |-> {"accepted", "total_cost", "budget_remaining"},
     observationFields |-> {"accepted", "total_cost", "budget_remaining"},
     implementationStateFields |-> {"accepted", "total_cost", "budget_remaining"},
     implementationStateMap |-> ImplementationStateMap,
     observationMap |-> ObservationMap,
     canonicalActions |-> {"AcceptNode"},
     systemActions |-> {"AcceptNode"},
     environmentActions |-> {},
     failureActions |-> {},
     commitActions |-> {"AcceptNode"},
     executableActions |-> {"accept_node"},
     actionMap |-> ActionMap,
     obligations |-> {"BudgetConsistency"},
     violations |-> {"SnapshotOverspend"},
     violationOf |-> ViolationOf,
     actors |-> {"allocation-claimant", "snapshot-authority"},
     claimant |-> "allocation-claimant",
     ownerOf |-> OwnerOf,
     delegateOf |-> DelegateOf,
     assuranceAt |-> AssuranceAt,
     relies |-> {"serialized-snapshot-mutation", "atomic-membership-cost-budget-commit", "complete-snapshot-writer-inventory"},
     guarantees |-> {"allocationsnapshot-written-profile-refinement", "snapshot-budget-consistency", "snapshot-atomic-admission", "snapshot-owner-ceiling"},
     runtimeProviders |-> {"snapshot-authority", "exclusive-mutation-provider", "bounded-integer-provider"},
     failureCeilings |-> {"no-modeled-crash-or-torn-snapshot", "concurrent-bypass-writers-outside-boundary", "finite-node-and-u64-representation-required"},
     executionCarriers |-> {"Sequential"},
     localTheorems |-> {"AllocationSnapshotImplRefinesSpec_Proof!RefinementThm", "AllocationSnapshot_Proof!Safety", "AllocationSnapshot_Proof!BudgetConsistencySafety", "TheoryKernel_Proof!ObligationPreservation", "TheoryKernel_Proof!CheckActStability", "OwnershipAssuranceKernel_Proof!OwnershipAssuranceClassification"},
     executablePointers |-> {"formal/structures/AllocationSnapshot/refinement/AllocationSnapshotImplRefinesSpec.tla", "formal/structures/AllocationSnapshot/refinement/AllocationSnapshotImplRefinesSpec_Proof.tla", "crate://automation-structures/0.2.3/src/compositions/allocation_snapshot.rs", "formal/structures/AllocationSnapshot/AllocationSnapshot.tla", "formal/structures/AllocationSnapshot/AllocationSnapshot_Proof.tla"},
     libraryPremises |-> {"AllocationSnapshot-written-contract-refinement-profile", "canonical-AcceptNode-machine", "BudgetConsistencySafety", "ObligationPreservation", "CheckActStability", "OwnershipAssuranceClassification"},
     deploymentPremises |-> {"NodesFinite", "BudgetCapacityType", "serialized-snapshot-mutation", "atomic-membership-cost-budget-commit", "complete-snapshot-writer-inventory"},
     residuals |-> {"formal-correspondence-is-limited-to-the-written-state-action-and-premise-map", "no-distributed-snapshot-protocol", "no-durability-or-recovery-result", "capture-order-is-not-a-priority-theorem"},
     evidenceCeilings |-> {"implementation-refinement-covers-only-the-written-bounded-contract-profile", "TLAPS-proves-the-canonical-Nat-budget-equation", "Verus-proves-duplicate-free-finite-vector-representation", "KAT-boundaries-do-not-establish-concurrency-safety"},
     validCases |-> {"accept-within-budget"},
     boundaryCases |-> {"exact-budget"},
     misuseCases |-> {"duplicate-node"},
     failureCases |-> {"torn-snapshot"},
     globalAssumptions |-> GlobalModelingAssumptionNames,
     conformanceConditions |-> ConformanceConditions,
     applicableFamilies |-> {"obligation", "check-act", "ownership-assurance", "refinement"},
     dischargedFamilies |-> {"obligation", "check-act", "ownership-assurance", "refinement"},
     transferClasses |-> {"safety"},
     refinementStatus |-> "mechanized",
     witnessStates |-> {"empty", "accepted", "overspent"},
     witnessInitial |-> {"empty"},
     witnessObligationStates |-> {"empty", "accepted"},
     witnessViolationStates |-> {"overspent"},
     witnessSystemSteps |-> {<<"empty", "accepted">>},
     witnessEnvironmentSteps |-> {},
     witnessActionSteps |-> WitnessActionSteps,
     witnessRelySteps |-> {},
     witnessCommitSteps |-> {<<"empty", "accepted">>},
     witnessFailureSteps |-> {},
     witnessInterferenceSteps |-> {},
     witnessCheckActMode |-> "atomic",
     witnessCheckResultStates |-> {"empty", "accepted"},
     witnessPredicateStates |-> {"empty", "accepted"},
     witnessActors |-> {"allocation-claimant", "snapshot-authority"},
     witnessProviders |-> {"snapshot-authority"},
     witnessClaimant |-> "allocation-claimant",
     witnessCommitOwner |-> "snapshot-authority",
     witnessCommitDelegate |-> "snapshot-authority",
     witnessAssuranceProvider |-> "snapshot-authority",
     witnessAssurancePosition |-> "at-commit",
     witnessPreventionControllers |-> {"snapshot-authority"},
     witnessUnavailableProviders |-> {},
     witnessPersistentObserve |-> WitnessPersistentObserve,
     witnessPersistentEvidence |-> TRUE,
     witnessRecoveryAvailable |-> FALSE,
     witnessActiveStates |-> {"empty", "accepted"},
     witnessClosedStates |-> {},
     witnessProgressSteps |-> {},
     witnessOtherSteps |-> {},
     witnessHandoffSteps |-> {},
     witnessRankBound |-> 0,
     witnessRank |-> WitnessRank,
     witnessFairnessOwners |-> {"snapshot-authority"},
     witnessFairnessOwner |-> "snapshot-authority",
     witnessFairnessOwnerOf |-> WitnessFairnessOwnerOf]

====
