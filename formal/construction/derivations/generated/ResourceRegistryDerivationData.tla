---- MODULE ResourceRegistryDerivationData ----
EXTENDS StructureDerivationSchema

\* Generated from the checked derivation record. Do not edit by hand.

ImplementationStateMap ==
    [key \in {"entries"} |->
        CASE key = "entries" -> "entries"
          [] OTHER -> "entries"]

ObservationMap ==
    [key \in {"entries"} |->
        CASE key = "entries" -> "entries"
          [] OTHER -> "entries"]

ActionMap ==
    [key \in {"Register", "Deregister"} |->
        CASE key = "Register" -> {"register"}
          [] key = "Deregister" -> {"deregister"}
          [] OTHER -> {"deregister"}]

ViolationOf ==
    [key \in {"UniqueMapping"} |->
        CASE key = "UniqueMapping" -> "DuplicateMapping"
          [] OTHER -> "DuplicateMapping"]

OwnerOf ==
    [key \in {"Register", "Deregister"} |->
        CASE key = "Register" -> "registry-authority"
          [] key = "Deregister" -> "registry-authority"
          [] OTHER -> "registry-authority"]

DelegateOf ==
    [key \in {"Register", "Deregister"} |->
        CASE key = "Register" -> {"registry-authority"}
          [] key = "Deregister" -> {"registry-authority"}
          [] OTHER -> {"registry-authority"}]

AssuranceAt ==
    [key \in {"Register", "Deregister"} |->
        CASE key = "Register" -> "at-commit"
          [] key = "Deregister" -> "at-commit"
          [] OTHER -> "at-commit"]

WitnessPersistentObserve ==
    [key \in {"empty", "single-a", "single-b", "duplicate"} |->
        CASE key = "empty" -> TRUE
          [] key = "single-a" -> TRUE
          [] key = "single-b" -> TRUE
          [] key = "duplicate" -> FALSE
          [] OTHER -> FALSE]

WitnessRank ==
    [key \in {"empty", "single-a", "single-b", "duplicate"} |->
        CASE key = "empty" -> 0
          [] key = "single-a" -> 0
          [] key = "single-b" -> 0
          [] key = "duplicate" -> 0
          [] OTHER -> 0]

WitnessFairnessOwnerOf == [key \in {} |-> "unused"]

WitnessActionSteps ==
    [key \in {"Register", "Deregister"} |->
        CASE key = "Register" -> {<<"empty", "single-a">>, <<"single-a", "single-b">>}
          [] key = "Deregister" -> {<<"single-a", "empty">>, <<"single-b", "empty">>}
          [] OTHER -> {<<"single-a", "empty">>, <<"single-b", "empty">>}]

Derivation ==
    [structure |-> "ResourceRegistry",
     kind |-> "abstraction-primitive",
     propertyClasses |-> {"safety"},
     stateFields |-> {"entries"},
     observationFields |-> {"entries"},
     implementationStateFields |-> {"entries"},
     implementationStateMap |-> ImplementationStateMap,
     observationMap |-> ObservationMap,
     canonicalActions |-> {"Register", "Deregister"},
     systemActions |-> {"Register", "Deregister"},
     environmentActions |-> {},
     failureActions |-> {},
     commitActions |-> {"Register", "Deregister"},
     executableActions |-> {"register", "deregister"},
     actionMap |-> ActionMap,
     obligations |-> {"UniqueMapping"},
     violations |-> {"DuplicateMapping"},
     violationOf |-> ViolationOf,
     actors |-> {"registry-client", "registry-authority"},
     claimant |-> "registry-client",
     ownerOf |-> OwnerOf,
     delegateOf |-> DelegateOf,
     assuranceAt |-> AssuranceAt,
     relies |-> {"serialized-exclusive-registry-mutation", "atomic-filter-and-replacement-or-removal", "complete-registry-writer-tcb-with-no-bypass"},
     guarantees |-> {"resourceregistry-written-profile-refinement", "unique-key-mapping", "atomic-upsert-license", "registry-owner-ceiling", "registry-executable-transfer"},
     runtimeProviders |-> {"registry-authority", "exclusive-mutation-provider", "key-value-representation"},
     failureCeilings |-> {"no-modeled-crash-torn-upsert-or-storage-loss", "concurrent-or-bypass-writers-outside-boundary", "u64-key-value-universe-is-an-executable-instantiation-not-a-universal-domain"},
     executionCarriers |-> {"Sequential"},
     localTheorems |-> {"ResourceRegistryImplRefinesSpec_Proof!RefinementThm", "ResourceRegistry_Proof!UniqueMappingSafety", "TheoryKernel_Proof!ObligationPreservation", "TheoryKernel_Proof!CheckActStability", "OwnershipAssuranceKernel_Proof!OwnershipAssuranceClassification"},
     executablePointers |-> {"formal/structures/ResourceRegistry/refinement/ResourceRegistryImplRefinesSpec.tla", "formal/structures/ResourceRegistry/refinement/ResourceRegistryImplRefinesSpec_Proof.tla", "development-copy://automation-structures/0.3.2/src/primitives/resource_registry.rs", "formal/structures/ResourceRegistry/ResourceRegistry.tla", "formal/structures/ResourceRegistry/ResourceRegistry_Proof.tla"},
     libraryPremises |-> {"ResourceRegistry-written-contract-refinement-profile", "canonical-two-action-partial-function-machine", "UniqueMappingSafety", "ObligationPreservation", "CheckActStability", "OwnershipAssuranceClassification"},
     deploymentPremises |-> {"Keys-and-Values-instantiated-by-the-executable-u64-universes", "serialized-exclusive-registry-mutation", "atomic-filter-and-replacement-or-removal", "complete-registry-writer-tcb-with-no-bypass"},
     residuals |-> {"formal-correspondence-is-limited-to-the-written-state-action-and-premise-map", "no-durable-distributed-or-versioned-registry-protocol", "lookup-is-a-derived-observation-not-a-canonical-state-transition", "authorization-for-which-client-may-bind-which-key-is-outside-UniqueMapping"},
     evidenceCeilings |-> {"implementation-refinement-covers-only-the-written-bounded-contract-profile", "TLAPS-proves-partial-function-uniqueness-for-the-canonical-set-machine", "Verus-proves-the-written-vector-pair-contracts-and-other-key-frames", "executable-semantic-transfer-is-limited-to-the-mapped-two-action-profile"},
     validCases |-> {"register-new-key", "replace-existing-key"},
     boundaryCases |-> {"deregister-present-key", "absent-deregister-rejected"},
     misuseCases |-> {"append-without-filter", "presence-only-frame"},
     failureCases |-> {"torn-upsert", "bypass-writer"},
     globalAssumptions |-> GlobalModelingAssumptionNames,
     conformanceConditions |-> ConformanceConditions,
     applicableFamilies |-> {"obligation", "check-act", "ownership-assurance", "refinement"},
     dischargedFamilies |-> {"obligation", "check-act", "ownership-assurance", "refinement"},
     transferClasses |-> {"safety", "observation"},
     refinementStatus |-> "mechanized",
     witnessStates |-> {"empty", "single-a", "single-b", "duplicate"},
     witnessInitial |-> {"empty"},
     witnessObligationStates |-> {"empty", "single-a", "single-b"},
     witnessViolationStates |-> {"duplicate"},
     witnessSystemSteps |-> {<<"empty", "single-a">>, <<"single-a", "single-b">>, <<"single-a", "empty">>, <<"single-b", "empty">>},
     witnessEnvironmentSteps |-> {},
     witnessActionSteps |-> WitnessActionSteps,
     witnessRelySteps |-> {},
     witnessCommitSteps |-> {<<"empty", "single-a">>, <<"single-a", "single-b">>, <<"single-a", "empty">>, <<"single-b", "empty">>},
     witnessFailureSteps |-> {},
     witnessInterferenceSteps |-> {},
     witnessCheckActMode |-> "atomic",
     witnessCheckResultStates |-> {"empty", "single-a", "single-b"},
     witnessPredicateStates |-> {"empty", "single-a", "single-b"},
     witnessActors |-> {"registry-client", "registry-authority"},
     witnessProviders |-> {"registry-authority"},
     witnessClaimant |-> "registry-client",
     witnessCommitOwner |-> "registry-authority",
     witnessCommitDelegate |-> "registry-authority",
     witnessAssuranceProvider |-> "registry-authority",
     witnessAssurancePosition |-> "at-commit",
     witnessPreventionControllers |-> {"registry-authority"},
     witnessUnavailableProviders |-> {},
     witnessPersistentObserve |-> WitnessPersistentObserve,
     witnessPersistentEvidence |-> TRUE,
     witnessRecoveryAvailable |-> FALSE,
     witnessActiveStates |-> {"empty", "single-a", "single-b"},
     witnessClosedStates |-> {},
     witnessProgressSteps |-> {},
     witnessOtherSteps |-> {},
     witnessHandoffSteps |-> {},
     witnessRankBound |-> 0,
     witnessRank |-> WitnessRank,
     witnessFairnessOwners |-> {"registry-authority"},
     witnessFairnessOwner |-> "registry-authority",
     witnessFairnessOwnerOf |-> WitnessFairnessOwnerOf]

====
