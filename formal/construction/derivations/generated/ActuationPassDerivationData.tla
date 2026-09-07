---- MODULE ActuationPassDerivationData ----
EXTENDS StructureDerivationSchema

\* Generated from the checked derivation record. Do not edit by hand.

ImplementationStateMap ==
    [key \in {"allocation", "effects", "complete"} |->
        CASE key = "allocation" -> "allocation"
          [] key = "effects" -> "effects"
          [] key = "complete" -> "complete"
          [] OTHER -> "complete"]

ObservationMap ==
    [key \in {"allocation", "effects", "complete"} |->
        CASE key = "allocation" -> "allocation"
          [] key = "effects" -> "effects"
          [] key = "complete" -> "complete"
          [] OTHER -> "complete"]

ActionMap ==
    [key \in {"Actuate", "Allocate", "Deallocate", "Finish"} |->
        CASE key = "Actuate" -> {"actuate"}
          [] key = "Allocate" -> {"allocate"}
          [] key = "Deallocate" -> {"deallocate"}
          [] key = "Finish" -> {"finish"}
          [] OTHER -> {"finish"}]

ViolationOf ==
    [key \in {"EffectFidelity", "PassCompleteness", "ActuationScope"} |->
        CASE key = "EffectFidelity" -> "EffectAllocationMismatch"
          [] key = "PassCompleteness" -> "IncompleteClosure"
          [] key = "ActuationScope" -> "ActuatedWithoutAllocation"
          [] OTHER -> "ActuatedWithoutAllocation"]

OwnerOf ==
    [key \in {"Actuate", "Allocate", "Deallocate", "Finish"} |->
        CASE key = "Actuate" -> "actuation-owner"
          [] key = "Allocate" -> "allocation-provider"
          [] key = "Deallocate" -> "allocation-provider"
          [] key = "Finish" -> "actuation-owner"
          [] OTHER -> "actuation-owner"]

DelegateOf ==
    [key \in {"Actuate", "Allocate", "Deallocate", "Finish"} |->
        CASE key = "Actuate" -> {"actuation-owner"}
          [] key = "Allocate" -> {"allocation-provider"}
          [] key = "Deallocate" -> {"allocation-provider"}
          [] key = "Finish" -> {"actuation-owner"}
          [] OTHER -> {"actuation-owner"}]

AssuranceAt ==
    [key \in {"Actuate", "Finish"} |->
        CASE key = "Actuate" -> "at-commit"
          [] key = "Finish" -> "at-commit"
          [] OTHER -> "at-commit"]

WitnessPersistentObserve ==
    [key \in {"idle", "allocated", "actuated", "complete", "wrong-effect", "incomplete-closed"} |->
        CASE key = "idle" -> TRUE
          [] key = "allocated" -> TRUE
          [] key = "actuated" -> TRUE
          [] key = "complete" -> TRUE
          [] key = "wrong-effect" -> FALSE
          [] key = "incomplete-closed" -> FALSE
          [] OTHER -> FALSE]

WitnessRank ==
    [key \in {"idle", "allocated", "actuated", "complete", "wrong-effect", "incomplete-closed"} |->
        CASE key = "idle" -> 0
          [] key = "allocated" -> 0
          [] key = "actuated" -> 0
          [] key = "complete" -> 0
          [] key = "wrong-effect" -> 0
          [] key = "incomplete-closed" -> 0
          [] OTHER -> 0]

WitnessFairnessOwnerOf == [key \in {} |-> "unused"]

WitnessActionSteps ==
    [key \in {"Actuate", "Allocate", "Deallocate", "Finish"} |->
        CASE key = "Actuate" -> {<<"allocated", "actuated">>}
          [] key = "Allocate" -> {<<"idle", "allocated">>}
          [] key = "Deallocate" -> {<<"allocated", "idle">>}
          [] key = "Finish" -> {<<"actuated", "complete">>, <<"idle", "complete">>}
          [] OTHER -> {<<"actuated", "complete">>, <<"idle", "complete">>}]

Derivation ==
    [structure |-> "ActuationPass",
     kind |-> "abstraction-primitive",
     propertyClasses |-> {"safety"},
     stateFields |-> {"allocation", "effects", "complete"},
     observationFields |-> {"allocation", "effects", "complete"},
     implementationStateFields |-> {"allocation", "effects", "complete"},
     implementationStateMap |-> ImplementationStateMap,
     observationMap |-> ObservationMap,
     canonicalActions |-> {"Actuate", "Allocate", "Deallocate", "Finish"},
     systemActions |-> {"Actuate", "Finish"},
     environmentActions |-> {"Allocate", "Deallocate"},
     failureActions |-> {},
     commitActions |-> {"Actuate", "Finish"},
     executableActions |-> {"actuate", "allocate", "deallocate", "finish"},
     actionMap |-> ActionMap,
     obligations |-> {"EffectFidelity", "PassCompleteness", "ActuationScope"},
     violations |-> {"EffectAllocationMismatch", "IncompleteClosure", "ActuatedWithoutAllocation"},
     violationOf |-> ViolationOf,
     actors |-> {"effect-requester", "actuation-owner", "allocation-provider"},
     claimant |-> "effect-requester",
     ownerOf |-> OwnerOf,
     delegateOf |-> DelegateOf,
     assuranceAt |-> AssuranceAt,
     relies |-> {"allocation-provider-respects-no-withdraw-after-effect", "atomic-allocation-read-and-effect-record", "atomic-completeness-check-and-finish", "serialized-pass-state-mutation", "complete-effect-and-allocation-writer-tcb"},
     guarantees |-> {"actuationpass-written-profile-refinement", "effect-fidelity", "truthful-pass-closure", "fused-actuation-and-finish-license", "actuation-owner-ceiling", "actuation-executable-transfer"},
     runtimeProviders |-> {"actuation-owner", "allocation-provider", "exclusive-mutation-provider", "external-effect-provider"},
     failureCeilings |-> {"the-model-records-an-effect-but-does-not-prove-an-external-effect-succeeded", "no-exactly-once-idempotence-compensation-or-recovery-result", "no-modeled-crash-torn-write-or-allocation-provider-failure", "concurrent-mutation-outside-the-serialized-boundary"},
     executionCarriers |-> {"Sequential"},
     localTheorems |-> {"ActuationPassImplRefinesSpec_Proof!RefinementThm", "ActuationPass_Proof!EffectFidelitySafety", "ActuationPass_Proof!PassCompletenessSafety", "ActuationPass_Proof!ActuationScopeSafety", "TheoryKernel_Proof!ObligationPreservation", "TheoryKernel_Proof!CheckActStability", "OwnershipAssuranceKernel_Proof!OwnershipAssuranceClassification"},
     executablePointers |-> {"formal/structures/ActuationPass/refinement/ActuationPassImplRefinesSpec.tla", "formal/structures/ActuationPass/refinement/ActuationPassImplRefinesSpec_Proof.tla", "crate://automation-structures/0.2.3/src/primitives/actuation_pass.rs", "formal/structures/ActuationPass/ActuationPass.tla", "formal/structures/ActuationPass/ActuationPass_Proof.tla"},
     libraryPremises |-> {"ActuationPass-written-contract-refinement-profile", "canonical-four-action-actuation-machine", "EffectFidelitySafety", "PassCompletenessSafety", "ActuationScopeSafety", "ObligationPreservation", "CheckActStability", "OwnershipAssuranceClassification"},
     deploymentPremises |-> {"Seats-and-Resources-instantiated-by-finite-executable-indices-and-u64-values", "allocation-provider-respects-no-withdraw-after-effect", "atomic-allocation-read-and-effect-record", "atomic-completeness-check-and-finish", "serialized-pass-state-mutation", "complete-effect-and-allocation-writer-tcb"},
     residuals |-> {"formal-correspondence-is-limited-to-the-written-state-action-and-premise-map", "effect-record-fidelity-is-not-proof-of-external-side-effect-success", "no-exactly-once-effect-claim", "allocation-lifecycle-after-pass-closure-is-outside-the-machine", "no-crash-retry-compensation-or-durable-effect-evidence-result"},
     evidenceCeilings |-> {"implementation-refinement-covers-only-the-written-bounded-contract-profile", "TLAPS-proves-the-three-written-state-obligations-with-no-module-level-assumption", "ActuationScope-is-a-derived-corollary-not-an-independent-effect-success-result", "Verus-proves-state-and-frame-contracts-under-exclusive-mutation", "executable-transfer-is-limited-to-the-mapped-state-record-and-closure-semantics"},
     validCases |-> {"fused-actuation", "truthful-finish"},
     boundaryCases |-> {"empty-pass-finish", "unapplied-deallocation"},
     misuseCases |-> {"split-allocation-read-effect-write", "finish-with-pending-seat"},
     failureCases |-> {"external-effect-fails-after-record", "withdraw-after-effect"},
     globalAssumptions |-> GlobalModelingAssumptionNames,
     conformanceConditions |-> ConformanceConditions,
     applicableFamilies |-> {"obligation", "check-act", "ownership-assurance", "refinement"},
     dischargedFamilies |-> {"obligation", "check-act", "ownership-assurance", "refinement"},
     transferClasses |-> {"safety", "observation"},
     refinementStatus |-> "mechanized",
     witnessStates |-> {"idle", "allocated", "actuated", "complete", "wrong-effect", "incomplete-closed"},
     witnessInitial |-> {"idle"},
     witnessObligationStates |-> {"idle", "allocated", "actuated", "complete"},
     witnessViolationStates |-> {"wrong-effect", "incomplete-closed"},
     witnessSystemSteps |-> {<<"allocated", "actuated">>, <<"actuated", "complete">>, <<"idle", "complete">>},
     witnessEnvironmentSteps |-> {<<"idle", "allocated">>, <<"allocated", "idle">>},
     witnessActionSteps |-> WitnessActionSteps,
     witnessRelySteps |-> {<<"idle", "allocated">>, <<"allocated", "idle">>},
     witnessCommitSteps |-> {<<"allocated", "actuated">>, <<"actuated", "complete">>, <<"idle", "complete">>},
     witnessFailureSteps |-> {},
     witnessInterferenceSteps |-> {<<"idle", "allocated">>, <<"allocated", "idle">>},
     witnessCheckActMode |-> "atomic",
     witnessCheckResultStates |-> {"idle", "allocated", "actuated"},
     witnessPredicateStates |-> {"idle", "allocated", "actuated", "complete"},
     witnessActors |-> {"effect-requester", "actuation-owner", "allocation-provider"},
     witnessProviders |-> {"actuation-owner", "allocation-provider"},
     witnessClaimant |-> "effect-requester",
     witnessCommitOwner |-> "actuation-owner",
     witnessCommitDelegate |-> "actuation-owner",
     witnessAssuranceProvider |-> "actuation-owner",
     witnessAssurancePosition |-> "at-commit",
     witnessPreventionControllers |-> {"actuation-owner"},
     witnessUnavailableProviders |-> {},
     witnessPersistentObserve |-> WitnessPersistentObserve,
     witnessPersistentEvidence |-> TRUE,
     witnessRecoveryAvailable |-> FALSE,
     witnessActiveStates |-> {"idle", "allocated", "actuated"},
     witnessClosedStates |-> {"complete", "wrong-effect", "incomplete-closed"},
     witnessProgressSteps |-> {},
     witnessOtherSteps |-> {},
     witnessHandoffSteps |-> {},
     witnessRankBound |-> 0,
     witnessRank |-> WitnessRank,
     witnessFairnessOwners |-> {"actuation-owner"},
     witnessFairnessOwner |-> "actuation-owner",
     witnessFairnessOwnerOf |-> WitnessFairnessOwnerOf]

====
