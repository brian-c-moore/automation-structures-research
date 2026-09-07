---- MODULE FederatedBudgetDerivationData ----
EXTENDS StructureDerivationSchema

\* Generated from the checked derivation record. Do not edit by hand.

ImplementationStateMap ==
    [key \in {"master_allocated", "sub_capacities", "sub_allocated"} |->
        CASE key = "master_allocated" -> "master_allocated"
          [] key = "sub_capacities" -> "sub_capacities"
          [] key = "sub_allocated" -> "sub_allocated"
          [] OTHER -> "sub_allocated"]

ObservationMap ==
    [key \in {"master_allocated", "sub_capacities", "sub_allocated"} |->
        CASE key = "master_allocated" -> "master_allocated"
          [] key = "sub_capacities" -> "sub_capacities"
          [] key = "sub_allocated" -> "sub_allocated"
          [] OTHER -> "sub_allocated"]

ActionMap ==
    [key \in {"AllocateSubPool", "AllocateFromSubPool", "ReleaseFromSubPool"} |->
        CASE key = "AllocateSubPool" -> {"allocate_sub_pool"}
          [] key = "AllocateFromSubPool" -> {"allocate_from_sub_pool"}
          [] key = "ReleaseFromSubPool" -> {"release_from_sub_pool"}
          [] OTHER -> {"release_from_sub_pool"}]

ViolationOf ==
    [key \in {"MasterCapacityBound", "SubPoolCapacityBound", "CapacityConservation"} |->
        CASE key = "MasterCapacityBound" -> "MasterOversubscription"
          [] key = "SubPoolCapacityBound" -> "SubPoolOversubscription"
          [] key = "CapacityConservation" -> "DelegatedCapacityMismatch"
          [] OTHER -> "DelegatedCapacityMismatch"]

OwnerOf ==
    [key \in {"AllocateSubPool", "AllocateFromSubPool", "ReleaseFromSubPool"} |->
        CASE key = "AllocateSubPool" -> "federated-budget-authority"
          [] key = "AllocateFromSubPool" -> "federated-budget-authority"
          [] key = "ReleaseFromSubPool" -> "federated-budget-authority"
          [] OTHER -> "federated-budget-authority"]

DelegateOf ==
    [key \in {"AllocateSubPool", "AllocateFromSubPool", "ReleaseFromSubPool"} |->
        CASE key = "AllocateSubPool" -> {"federated-budget-authority"}
          [] key = "AllocateFromSubPool" -> {"federated-budget-authority"}
          [] key = "ReleaseFromSubPool" -> {"federated-budget-authority"}
          [] OTHER -> {"federated-budget-authority"}]

AssuranceAt ==
    [key \in {"AllocateSubPool", "AllocateFromSubPool", "ReleaseFromSubPool"} |->
        CASE key = "AllocateSubPool" -> "at-commit"
          [] key = "AllocateFromSubPool" -> "at-commit"
          [] key = "ReleaseFromSubPool" -> "at-commit"
          [] OTHER -> "at-commit"]

WitnessPersistentObserve ==
    [key \in {"empty", "delegated", "consumed", "inconsistent-capacity"} |->
        CASE key = "empty" -> TRUE
          [] key = "delegated" -> TRUE
          [] key = "consumed" -> TRUE
          [] key = "inconsistent-capacity" -> FALSE
          [] OTHER -> FALSE]

WitnessRank ==
    [key \in {"empty", "delegated", "consumed", "inconsistent-capacity"} |->
        CASE key = "empty" -> 0
          [] key = "delegated" -> 0
          [] key = "consumed" -> 0
          [] key = "inconsistent-capacity" -> 0
          [] OTHER -> 0]

WitnessFairnessOwnerOf == [key \in {} |-> "unused"]

WitnessActionSteps ==
    [key \in {"AllocateSubPool", "AllocateFromSubPool", "ReleaseFromSubPool"} |->
        CASE key = "AllocateSubPool" -> {<<"empty", "delegated">>}
          [] key = "AllocateFromSubPool" -> {<<"delegated", "consumed">>}
          [] key = "ReleaseFromSubPool" -> {<<"consumed", "delegated">>}
          [] OTHER -> {<<"consumed", "delegated">>}]

Derivation ==
    [structure |-> "FederatedBudget",
     kind |-> "named-composition",
     propertyClasses |-> {"safety"},
     stateFields |-> {"master_allocated", "sub_capacities", "sub_allocated"},
     observationFields |-> {"master_allocated", "sub_capacities", "sub_allocated"},
     implementationStateFields |-> {"master_allocated", "sub_capacities", "sub_allocated"},
     implementationStateMap |-> ImplementationStateMap,
     observationMap |-> ObservationMap,
     canonicalActions |-> {"AllocateSubPool", "AllocateFromSubPool", "ReleaseFromSubPool"},
     systemActions |-> {"AllocateSubPool", "AllocateFromSubPool", "ReleaseFromSubPool"},
     environmentActions |-> {},
     failureActions |-> {},
     commitActions |-> {"AllocateSubPool", "AllocateFromSubPool", "ReleaseFromSubPool"},
     executableActions |-> {"allocate_sub_pool", "allocate_from_sub_pool", "release_from_sub_pool"},
     actionMap |-> ActionMap,
     obligations |-> {"MasterCapacityBound", "SubPoolCapacityBound", "CapacityConservation"},
     violations |-> {"MasterOversubscription", "SubPoolOversubscription", "DelegatedCapacityMismatch"},
     violationOf |-> ViolationOf,
     actors |-> {"budget-claimant", "federated-budget-authority"},
     claimant |-> "budget-claimant",
     ownerOf |-> OwnerOf,
     delegateOf |-> DelegateOf,
     assuranceAt |-> AssuranceAt,
     relies |-> {"finite-subpool-name-set", "serialized-master-and-subpool-mutation", "atomic-delegation-conservation-update"},
     guarantees |-> {"federatedbudget-written-profile-refinement", "federated-capacity-safety", "atomic-delegation-license", "federated-owner-ceiling"},
     runtimeProviders |-> {"federated-budget-authority", "finite-subpool-provider", "exclusive-mutation-provider"},
     failureCeilings |-> {"no-modeled-partial-failure-or-torn-delegation", "concurrent-bypass-writer-outside-boundary", "centralized-atomic-state-not-a-distributed-federation-protocol"},
     executionCarriers |-> {"Sequential"},
     localTheorems |-> {"FederatedBudgetImplRefinesSpec_Proof!RefinementThm", "FederatedBudget_Proof!Safety", "FederatedBudget_Proof!MasterCapacityBoundSafety", "FederatedBudget_Proof!SubPoolCapacityBoundSafety", "FederatedBudget_Proof!CapacityConservationSafety", "TheoryKernel_Proof!ObligationPreservation", "TheoryKernel_Proof!CheckActStability", "OwnershipAssuranceKernel_Proof!OwnershipAssuranceClassification"},
     executablePointers |-> {"formal/structures/FederatedBudget/refinement/FederatedBudgetImplRefinesSpec.tla", "formal/structures/FederatedBudget/refinement/FederatedBudgetImplRefinesSpec_Proof.tla", "crate://automation-structures/0.2.3/src/compositions/federated_budget.rs", "formal/structures/FederatedBudget/FederatedBudget.tla", "formal/structures/FederatedBudget/FederatedBudget_Proof.tla"},
     libraryPremises |-> {"FederatedBudget-written-contract-refinement-profile", "canonical-federated-budget-machine", "FederatedBudget-Safety", "ObligationPreservation", "CheckActStability", "OwnershipAssuranceClassification"},
     deploymentPremises |-> {"SubPoolNamesFinite", "MasterCapacityType", "serialized-master-and-subpool-mutation", "atomic-delegation-conservation-update", "complete-budget-writer-inventory"},
     residuals |-> {"formal-correspondence-is-limited-to-the-written-state-action-and-premise-map", "no-independent-subpool-failure-model", "no-reclamation-of-delegated-capacity", "no-distributed-consensus-or-partition-tolerance-result"},
     evidenceCeilings |-> {"implementation-refinement-covers-only-the-written-bounded-contract-profile", "TLAPS-proves-the-parametric-finite-sum-capacity-machine", "Verus-proves-the-written-centralized-vector-carrier", "the-name-federated-does-not-imply-distributed-fault-tolerance"},
     validCases |-> {"delegate-consume-release"},
     boundaryCases |-> {"exact-master-capacity"},
     misuseCases |-> {"subpool-oversubscription"},
     failureCases |-> {"torn-delegation"},
     globalAssumptions |-> GlobalModelingAssumptionNames,
     conformanceConditions |-> ConformanceConditions,
     applicableFamilies |-> {"obligation", "check-act", "ownership-assurance", "refinement"},
     dischargedFamilies |-> {"obligation", "check-act", "ownership-assurance", "refinement"},
     transferClasses |-> {"safety"},
     refinementStatus |-> "mechanized",
     witnessStates |-> {"empty", "delegated", "consumed", "inconsistent-capacity"},
     witnessInitial |-> {"empty"},
     witnessObligationStates |-> {"empty", "delegated", "consumed"},
     witnessViolationStates |-> {"inconsistent-capacity"},
     witnessSystemSteps |-> {<<"empty", "delegated">>, <<"delegated", "consumed">>, <<"consumed", "delegated">>},
     witnessEnvironmentSteps |-> {},
     witnessActionSteps |-> WitnessActionSteps,
     witnessRelySteps |-> {},
     witnessCommitSteps |-> {<<"empty", "delegated">>, <<"delegated", "consumed">>, <<"consumed", "delegated">>},
     witnessFailureSteps |-> {},
     witnessInterferenceSteps |-> {},
     witnessCheckActMode |-> "atomic",
     witnessCheckResultStates |-> {"empty", "delegated", "consumed"},
     witnessPredicateStates |-> {"empty", "delegated", "consumed"},
     witnessActors |-> {"budget-claimant", "federated-budget-authority"},
     witnessProviders |-> {"federated-budget-authority"},
     witnessClaimant |-> "budget-claimant",
     witnessCommitOwner |-> "federated-budget-authority",
     witnessCommitDelegate |-> "federated-budget-authority",
     witnessAssuranceProvider |-> "federated-budget-authority",
     witnessAssurancePosition |-> "at-commit",
     witnessPreventionControllers |-> {"federated-budget-authority"},
     witnessUnavailableProviders |-> {},
     witnessPersistentObserve |-> WitnessPersistentObserve,
     witnessPersistentEvidence |-> TRUE,
     witnessRecoveryAvailable |-> FALSE,
     witnessActiveStates |-> {"empty", "delegated", "consumed"},
     witnessClosedStates |-> {},
     witnessProgressSteps |-> {},
     witnessOtherSteps |-> {},
     witnessHandoffSteps |-> {},
     witnessRankBound |-> 0,
     witnessRank |-> WitnessRank,
     witnessFairnessOwners |-> {"federated-budget-authority"},
     witnessFairnessOwner |-> "federated-budget-authority",
     witnessFairnessOwnerOf |-> WitnessFairnessOwnerOf]

====
