---- MODULE SamplerDerivationData ----
EXTENDS StructureDerivationSchema

\* Generated from the checked derivation record. Do not edit by hand.

ImplementationStateMap ==
    [key \in {"distribution", "selected"} |->
        CASE key = "distribution" -> "distribution"
          [] key = "selected" -> "selected"
          [] OTHER -> "selected"]

ObservationMap ==
    [key \in {"distribution", "selected"} |->
        CASE key = "distribution" -> "distribution"
          [] key = "selected" -> "selected"
          [] OTHER -> "selected"]

ActionMap ==
    [key \in {"Sample", "Zero"} |->
        CASE key = "Sample" -> {"sample", "draw_weighted", "draw_uniform"}
          [] key = "Zero" -> {"zero"}
          [] OTHER -> {"zero"}]

ViolationOf ==
    [key \in {"BoundedSample", "SupportConsistency"} |->
        CASE key = "BoundedSample" -> "SampleSizeExceeded"
          [] key = "SupportConsistency" -> "SelectionOutsideSupport"
          [] OTHER -> "SelectionOutsideSupport"]

OwnerOf ==
    [key \in {"Sample", "Zero"} |->
        CASE key = "Sample" -> "sampling-authority"
          [] key = "Zero" -> "distribution-provider"
          [] OTHER -> "distribution-provider"]

DelegateOf ==
    [key \in {"Sample", "Zero"} |->
        CASE key = "Sample" -> {"sampling-authority"}
          [] key = "Zero" -> {"distribution-provider"}
          [] OTHER -> {"distribution-provider"}]

AssuranceAt ==
    [key \in {"Sample"} |->
        CASE key = "Sample" -> "at-commit"
          [] OTHER -> "at-commit"]

WitnessPersistentObserve ==
    [key \in {"live-support", "sampled", "unsupported-selection"} |->
        CASE key = "live-support" -> TRUE
          [] key = "sampled" -> TRUE
          [] key = "unsupported-selection" -> FALSE
          [] OTHER -> FALSE]

WitnessRank ==
    [key \in {"live-support", "sampled", "unsupported-selection"} |->
        CASE key = "live-support" -> 0
          [] key = "sampled" -> 0
          [] key = "unsupported-selection" -> 0
          [] OTHER -> 0]

WitnessFairnessOwnerOf == [key \in {} |-> "unused"]

WitnessActionSteps ==
    [key \in {"Sample", "Zero"} |->
        CASE key = "Sample" -> {<<"live-support", "sampled">>}
          [] key = "Zero" -> {<<"sampled", "sampled">>}
          [] OTHER -> {<<"sampled", "sampled">>}]

Derivation ==
    [structure |-> "Sampler",
     kind |-> "named-composition",
     propertyClasses |-> {"safety"},
     stateFields |-> {"distribution", "selected"},
     observationFields |-> {"distribution", "selected"},
     implementationStateFields |-> {"distribution", "selected"},
     implementationStateMap |-> ImplementationStateMap,
     observationMap |-> ObservationMap,
     canonicalActions |-> {"Sample", "Zero"},
     systemActions |-> {"Sample"},
     environmentActions |-> {"Zero"},
     failureActions |-> {},
     commitActions |-> {"Sample"},
     executableActions |-> {"sample", "draw_weighted", "draw_uniform", "zero"},
     actionMap |-> ActionMap,
     obligations |-> {"BoundedSample", "SupportConsistency"},
     violations |-> {"SampleSizeExceeded", "SelectionOutsideSupport"},
     violationOf |-> ViolationOf,
     actors |-> {"sampling-claimant", "sampling-authority", "distribution-provider"},
     claimant |-> "sampling-claimant",
     ownerOf |-> OwnerOf,
     delegateOf |-> DelegateOf,
     assuranceAt |-> AssuranceAt,
     relies |-> {"finite-item-universe", "serialized-distribution-selection-mutation", "atomic-support-check-and-selection"},
     guarantees |-> {"sampler-written-profile-refinement", "bounded-supported-selection", "atomic-support-license", "sampler-owner-ceiling"},
     runtimeProviders |-> {"sampling-authority", "distribution-provider", "exclusive-mutation-provider", "draw-input-provider"},
     failureCeilings |-> {"no-randomness-quality-or-distribution-convergence-claim", "no-modeled-crash-or-torn-selection", "concurrent-support-writer-outside-boundary"},
     executionCarriers |-> {"Sequential"},
     localTheorems |-> {"SamplerImplRefinesSpec_Proof!RefinementThm", "Sampler_Proof!Safety", "Sampler_Proof!BoundedSampleSafety", "Sampler_Proof!SupportConsistencySafety", "TheoryKernel_Proof!ObligationPreservation", "TheoryKernel_Proof!CheckActStability", "OwnershipAssuranceKernel_Proof!OwnershipAssuranceClassification"},
     executablePointers |-> {"formal/structures/Sampler/refinement/SamplerImplRefinesSpec.tla", "formal/structures/Sampler/refinement/SamplerImplRefinesSpec_Proof.tla", "crate://automation-structures/0.2.3/src/compositions/sampler.rs", "formal/structures/Sampler/Sampler.tla", "formal/structures/Sampler/Sampler_Proof.tla"},
     libraryPremises |-> {"Sampler-written-contract-refinement-profile", "canonical-sample-zero-machine", "Sampler-Safety", "ObligationPreservation", "CheckActStability", "OwnershipAssuranceClassification"},
     deploymentPremises |-> {"ItemsFinite", "SampleSizeType", "MaxProbType", "serialized-distribution-selection-mutation", "atomic-support-check-and-selection"},
     residuals |-> {"formal-correspondence-is-limited-to-the-written-state-action-and-premise-map", "no-randomness-quality-result", "no-fair-selection-or-frequency-result", "all-zero-policy-is-an-explicit-rejection-boundary"},
     evidenceCeilings |-> {"implementation-refinement-covers-only-the-written-bounded-contract-profile", "TLAPS-proves-only-bounds-and-support", "Verus-draw-input-is-caller-supplied-not-randomness-proof", "KAT-draw-boundaries-are-cross-checks-only"},
     validCases |-> {"supported-fresh-draw"},
     boundaryCases |-> {"sample-size-full"},
     misuseCases |-> {"zero-support-draw"},
     failureCases |-> {"concurrent-zero-and-draw"},
     globalAssumptions |-> GlobalModelingAssumptionNames,
     conformanceConditions |-> ConformanceConditions,
     applicableFamilies |-> {"obligation", "check-act", "ownership-assurance", "refinement"},
     dischargedFamilies |-> {"obligation", "check-act", "ownership-assurance", "refinement"},
     transferClasses |-> {"safety"},
     refinementStatus |-> "mechanized",
     witnessStates |-> {"live-support", "sampled", "unsupported-selection"},
     witnessInitial |-> {"live-support"},
     witnessObligationStates |-> {"live-support", "sampled"},
     witnessViolationStates |-> {"unsupported-selection"},
     witnessSystemSteps |-> {<<"live-support", "sampled">>},
     witnessEnvironmentSteps |-> {<<"sampled", "sampled">>},
     witnessActionSteps |-> WitnessActionSteps,
     witnessRelySteps |-> {<<"sampled", "sampled">>},
     witnessCommitSteps |-> {<<"live-support", "sampled">>},
     witnessFailureSteps |-> {},
     witnessInterferenceSteps |-> {},
     witnessCheckActMode |-> "atomic",
     witnessCheckResultStates |-> {"live-support", "sampled"},
     witnessPredicateStates |-> {"live-support", "sampled"},
     witnessActors |-> {"sampling-claimant", "sampling-authority", "distribution-provider"},
     witnessProviders |-> {"sampling-authority", "distribution-provider"},
     witnessClaimant |-> "sampling-claimant",
     witnessCommitOwner |-> "sampling-authority",
     witnessCommitDelegate |-> "sampling-authority",
     witnessAssuranceProvider |-> "sampling-authority",
     witnessAssurancePosition |-> "at-commit",
     witnessPreventionControllers |-> {"sampling-authority"},
     witnessUnavailableProviders |-> {},
     witnessPersistentObserve |-> WitnessPersistentObserve,
     witnessPersistentEvidence |-> TRUE,
     witnessRecoveryAvailable |-> FALSE,
     witnessActiveStates |-> {"live-support", "sampled"},
     witnessClosedStates |-> {},
     witnessProgressSteps |-> {},
     witnessOtherSteps |-> {},
     witnessHandoffSteps |-> {},
     witnessRankBound |-> 0,
     witnessRank |-> WitnessRank,
     witnessFairnessOwners |-> {"sampling-authority"},
     witnessFairnessOwner |-> "sampling-authority",
     witnessFairnessOwnerOf |-> WitnessFairnessOwnerOf]

====
