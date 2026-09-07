---- MODULE ReductionDerivationData ----
EXTENDS StructureDerivationSchema

\* Generated from the checked derivation record. Do not edit by hand.

ImplementationStateMap ==
    [key \in {"result", "pos"} |->
        CASE key = "result" -> "result"
          [] key = "pos" -> "pos"
          [] OTHER -> "pos"]

ObservationMap ==
    [key \in {"result", "pos"} |->
        CASE key = "result" -> "result"
          [] key = "pos" -> "pos"
          [] OTHER -> "pos"]

ActionMap ==
    [key \in {"Consume"} |->
        CASE key = "Consume" -> {"process"}
          [] OTHER -> {"process"}]

ViolationOf ==
    [key \in {"ConsumedPrefixFold"} |->
        CASE key = "ConsumedPrefixFold" -> "ResultPrefixMismatch"
          [] OTHER -> "ResultPrefixMismatch"]

OwnerOf ==
    [key \in {"Consume"} |->
        CASE key = "Consume" -> "reduction-authority"
          [] OTHER -> "reduction-authority"]

DelegateOf ==
    [key \in {"Consume"} |->
        CASE key = "Consume" -> {"reduction-authority"}
          [] OTHER -> {"reduction-authority"}]

AssuranceAt ==
    [key \in {"Consume"} |->
        CASE key = "Consume" -> "at-commit"
          [] OTHER -> "at-commit"]

WitnessPersistentObserve ==
    [key \in {"empty-prefix", "partial-prefix", "complete-prefix", "mismatched-prefix"} |->
        CASE key = "empty-prefix" -> TRUE
          [] key = "partial-prefix" -> TRUE
          [] key = "complete-prefix" -> TRUE
          [] key = "mismatched-prefix" -> FALSE
          [] OTHER -> FALSE]

WitnessRank ==
    [key \in {"empty-prefix", "partial-prefix", "complete-prefix", "mismatched-prefix"} |->
        CASE key = "empty-prefix" -> 0
          [] key = "partial-prefix" -> 0
          [] key = "complete-prefix" -> 0
          [] key = "mismatched-prefix" -> 0
          [] OTHER -> 0]

WitnessFairnessOwnerOf == [key \in {} |-> "unused"]

WitnessActionSteps ==
    [key \in {"Consume"} |->
        CASE key = "Consume" -> {<<"empty-prefix", "partial-prefix">>, <<"partial-prefix", "complete-prefix">>}
          [] OTHER -> {<<"empty-prefix", "partial-prefix">>, <<"partial-prefix", "complete-prefix">>}]

Derivation ==
    [structure |-> "Reduction",
     kind |-> "named-composition",
     propertyClasses |-> {"safety"},
     stateFields |-> {"result", "pos"},
     observationFields |-> {"result", "pos"},
     implementationStateFields |-> {"result", "pos"},
     implementationStateMap |-> ImplementationStateMap,
     observationMap |-> ObservationMap,
     canonicalActions |-> {"Consume"},
     systemActions |-> {"Consume"},
     environmentActions |-> {},
     failureActions |-> {},
     commitActions |-> {"Consume"},
     executableActions |-> {"process"},
     actionMap |-> ActionMap,
     obligations |-> {"ConsumedPrefixFold"},
     violations |-> {"ResultPrefixMismatch"},
     violationOf |-> ViolationOf,
     actors |-> {"reduction-claimant", "reduction-authority"},
     claimant |-> "reduction-claimant",
     ownerOf |-> OwnerOf,
     delegateOf |-> DelegateOf,
     assuranceAt |-> AssuranceAt,
     relies |-> {"immutable-ordered-source", "operator-closure-on-natural-values", "serialized-result-position-mutation"},
     guarantees |-> {"reduction-written-profile-refinement", "ordered-prefix-fold-safety", "atomic-consume-license", "reduction-owner-ceiling"},
     runtimeProviders |-> {"reduction-authority", "ordered-source-provider", "operator-provider"},
     failureCeilings |-> {"no-modeled-crash-or-torn-result-position", "source-mutation-outside-boundary", "no-concurrent-or-reordered-reduction-schedule"},
     executionCarriers |-> {"Sequential"},
     localTheorems |-> {"ReductionImplRefinesSpec_Proof!RefinementThm", "ReductionStream_Proof!Safety", "ReductionStream_Proof!ConsumedPrefixFoldSafety", "TheoryKernel_Proof!ObligationPreservation", "TheoryKernel_Proof!CheckActStability", "OwnershipAssuranceKernel_Proof!OwnershipAssuranceClassification"},
     executablePointers |-> {"formal/structures/Reduction/refinement/ReductionImplRefinesSpec.tla", "formal/structures/Reduction/refinement/ReductionImplRefinesSpec_Proof.tla", "crate://automation-structures/0.2.3/src/compositions/reduction.rs", "formal/structures/Reduction/ReductionStream.tla", "formal/structures/Reduction/ReductionStream_Proof.tla"},
     libraryPremises |-> {"Reduction-written-contract-refinement-profile", "canonical-ordered-stream-reduction-machine", "ReductionStream-Safety", "ConsumedPrefixFoldSafety", "ObligationPreservation", "CheckActStability", "OwnershipAssuranceClassification"},
     deploymentPremises |-> {"IdentityType", "SrcLen", "SrcNat", "OpType", "immutable-ordered-source", "serialized-result-position-mutation"},
     residuals |-> {"formal-correspondence-is-limited-to-the-written-state-action-and-premise-map", "no-eventual-full-consumption-result", "no-reordering-or-parallel-tree-equivalence", "no-overflow-transfer-beyond-the-written-u64-carrier-preconditions"},
     evidenceCeilings |-> {"implementation-refinement-covers-only-the-written-bounded-contract-profile", "TLAPS-proves-the-parametric-ordered-consumed-prefix-fold", "Verus-proves-written-sum-and-max-carriers-under-their-preconditions", "exactly-once-means-prefix-contribution-not-durable-message-processing"},
     validCases |-> {"consume-next-prefix-element"},
     boundaryCases |-> {"empty-prefix"},
     misuseCases |-> {"reordered-or-duplicated-contribution"},
     failureCases |-> {"torn-result-position"},
     globalAssumptions |-> GlobalModelingAssumptionNames,
     conformanceConditions |-> ConformanceConditions,
     applicableFamilies |-> {"obligation", "check-act", "ownership-assurance", "refinement"},
     dischargedFamilies |-> {"obligation", "check-act", "ownership-assurance", "refinement"},
     transferClasses |-> {"safety"},
     refinementStatus |-> "mechanized",
     witnessStates |-> {"empty-prefix", "partial-prefix", "complete-prefix", "mismatched-prefix"},
     witnessInitial |-> {"empty-prefix"},
     witnessObligationStates |-> {"empty-prefix", "partial-prefix", "complete-prefix"},
     witnessViolationStates |-> {"mismatched-prefix"},
     witnessSystemSteps |-> {<<"empty-prefix", "partial-prefix">>, <<"partial-prefix", "complete-prefix">>},
     witnessEnvironmentSteps |-> {},
     witnessActionSteps |-> WitnessActionSteps,
     witnessRelySteps |-> {},
     witnessCommitSteps |-> {<<"empty-prefix", "partial-prefix">>, <<"partial-prefix", "complete-prefix">>},
     witnessFailureSteps |-> {},
     witnessInterferenceSteps |-> {},
     witnessCheckActMode |-> "atomic",
     witnessCheckResultStates |-> {"empty-prefix", "partial-prefix", "complete-prefix"},
     witnessPredicateStates |-> {"empty-prefix", "partial-prefix", "complete-prefix"},
     witnessActors |-> {"reduction-claimant", "reduction-authority"},
     witnessProviders |-> {"reduction-authority"},
     witnessClaimant |-> "reduction-claimant",
     witnessCommitOwner |-> "reduction-authority",
     witnessCommitDelegate |-> "reduction-authority",
     witnessAssuranceProvider |-> "reduction-authority",
     witnessAssurancePosition |-> "at-commit",
     witnessPreventionControllers |-> {"reduction-authority"},
     witnessUnavailableProviders |-> {},
     witnessPersistentObserve |-> WitnessPersistentObserve,
     witnessPersistentEvidence |-> TRUE,
     witnessRecoveryAvailable |-> FALSE,
     witnessActiveStates |-> {"empty-prefix", "partial-prefix", "complete-prefix"},
     witnessClosedStates |-> {},
     witnessProgressSteps |-> {},
     witnessOtherSteps |-> {},
     witnessHandoffSteps |-> {},
     witnessRankBound |-> 0,
     witnessRank |-> WitnessRank,
     witnessFairnessOwners |-> {"reduction-authority"},
     witnessFairnessOwner |-> "reduction-authority",
     witnessFairnessOwnerOf |-> WitnessFairnessOwnerOf]

====
