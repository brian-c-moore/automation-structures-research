---- MODULE ConvergenceGovernorDerivationData ----
EXTENDS StructureDerivationSchema

\* Generated from the checked derivation record. Do not edit by hand.

ImplementationStateMap ==
    [key \in {"state", "gradient_phase", "delta_history", "peak_observed"} |->
        CASE key = "state" -> "state"
          [] key = "gradient_phase" -> "gradient_phase"
          [] key = "delta_history" -> "delta_history"
          [] key = "peak_observed" -> "peak_observed"
          [] OTHER -> "peak_observed"]

ObservationMap ==
    [key \in {"state", "gradient_phase", "delta_history", "peak_observed"} |->
        CASE key = "state" -> "state"
          [] key = "gradient_phase" -> "gradient_phase"
          [] key = "delta_history" -> "delta_history"
          [] key = "peak_observed" -> "peak_observed"
          [] OTHER -> "peak_observed"]

ActionMap ==
    [key \in {"Update"} |->
        CASE key = "Update" -> {"update"}
          [] OTHER -> {"update"}]

ViolationOf ==
    [key \in {"NoCoolingFromCold", "ConvergenceRequiresHistory", "ValidTransitionsProp"} |->
        CASE key = "NoCoolingFromCold" -> "CoolingWithoutPeakPhase"
          [] key = "ConvergenceRequiresHistory" -> "ConvergedWithoutPeakHistory"
          [] key = "ValidTransitionsProp" -> "InvalidGovernorTransition"
          [] OTHER -> "InvalidGovernorTransition"]

OwnerOf ==
    [key \in {"Update"} |->
        CASE key = "Update" -> "governor-authority"
          [] OTHER -> "governor-authority"]

DelegateOf ==
    [key \in {"Update"} |->
        CASE key = "Update" -> {"governor-authority"}
          [] OTHER -> {"governor-authority"}]

AssuranceAt ==
    [key \in {"Update"} |->
        CASE key = "Update" -> "at-commit"
          [] OTHER -> "at-commit"]

WitnessPersistentObserve ==
    [key \in {"active-cold", "cooling", "converged", "invalid-transition"} |->
        CASE key = "active-cold" -> TRUE
          [] key = "cooling" -> TRUE
          [] key = "converged" -> TRUE
          [] key = "invalid-transition" -> FALSE
          [] OTHER -> FALSE]

WitnessRank ==
    [key \in {"active-cold", "cooling", "converged", "invalid-transition"} |->
        CASE key = "active-cold" -> 0
          [] key = "cooling" -> 0
          [] key = "converged" -> 0
          [] key = "invalid-transition" -> 0
          [] OTHER -> 0]

WitnessFairnessOwnerOf == [key \in {} |-> "unused"]

WitnessActionSteps ==
    [key \in {"Update"} |->
        CASE key = "Update" -> {<<"active-cold", "cooling">>, <<"cooling", "converged">>, <<"converged", "converged">>}
          [] OTHER -> {<<"active-cold", "cooling">>, <<"cooling", "converged">>, <<"converged", "converged">>}]

Derivation ==
    [structure |-> "ConvergenceGovernor",
     kind |-> "abstraction-primitive",
     propertyClasses |-> {"safety"},
     stateFields |-> {"state", "gradient_phase", "delta_history", "peak_observed"},
     observationFields |-> {"state", "gradient_phase", "delta_history", "peak_observed"},
     implementationStateFields |-> {"state", "gradient_phase", "delta_history", "peak_observed"},
     implementationStateMap |-> ImplementationStateMap,
     observationMap |-> ObservationMap,
     canonicalActions |-> {"Update"},
     systemActions |-> {"Update"},
     environmentActions |-> {},
     failureActions |-> {},
     commitActions |-> {"Update"},
     executableActions |-> {"update"},
     actionMap |-> ActionMap,
     obligations |-> {"NoCoolingFromCold", "ConvergenceRequiresHistory", "ValidTransitionsProp"},
     violations |-> {"CoolingWithoutPeakPhase", "ConvergedWithoutPeakHistory", "InvalidGovernorTransition"},
     violationOf |-> ViolationOf,
     actors |-> {"governor-claimant", "governor-authority", "delta-provider"},
     claimant |-> "governor-claimant",
     ownerOf |-> OwnerOf,
     delegateOf |-> DelegateOf,
     assuranceAt |-> AssuranceAt,
     relies |-> {"bounded-delta-input", "caller-supplied-exact-post-slide-average", "serialized-governor-state-mutation"},
     guarantees |-> {"convergencegovernor-written-profile-refinement", "phase-aware-governor-safety", "valid-governor-transition", "atomic-governor-license", "governor-owner-ceiling"},
     runtimeProviders |-> {"governor-authority", "delta-provider", "post-slide-average-provider"},
     failureCeilings |-> {"no-modeled-crash-or-torn-governor-update", "incorrect-caller-average-outside-rely", "input-sequence-may-stay-active-forever"},
     executionCarriers |-> {"Sequential"},
     localTheorems |-> {"ConvergenceGovernorImplRefinesSpec_Proof!RefinementThm", "ConvergenceGovernorPhaseAware_Proof!Safety", "ConvergenceGovernorPhaseAware_Proof!ValidTransitionsSafety", "ConvergenceGovernorPhaseAware_Proof!ConvergedRequiresPeakSafety", "TheoryKernel_Proof!ObligationPreservation", "TheoryKernel_Proof!CheckActStability", "OwnershipAssuranceKernel_Proof!OwnershipAssuranceClassification"},
     executablePointers |-> {"formal/structures/ConvergenceGovernor/refinement/ConvergenceGovernorImplRefinesSpec.tla", "formal/structures/ConvergenceGovernor/refinement/ConvergenceGovernorImplRefinesSpec_Proof.tla", "crate://automation-structures/0.2.3/src/primitives/convergence_governor_phase_aware.rs", "formal/structures/ConvergenceGovernor/ConvergenceGovernorPhaseAware.tla", "formal/structures/ConvergenceGovernor/ConvergenceGovernorPhaseAware_Proof.tla"},
     libraryPremises |-> {"ConvergenceGovernor-written-contract-refinement-profile", "canonical-phase-aware-governor-machine", "ConvergenceGovernor-Safety", "ValidTransitionsSafety", "ObligationPreservation", "CheckActStability", "OwnershipAssuranceClassification"},
     deploymentPremises |-> {"ThresholdType", "AwakenThresholdType", "WindowType", "MaxDeltaType", "caller-supplied-exact-post-slide-average", "serialized-governor-state-mutation"},
     residuals |-> {"formal-correspondence-is-limited-to-the-written-state-action-and-premise-map", "no-eventual-convergence-or-termination-result", "no-monotone-delta-sequence-claim", "no-time-bound-or-statistical-convergence-theorem"},
     evidenceCeilings |-> {"implementation-refinement-covers-only-the-written-bounded-contract-profile", "TLAPS-proves-phase-history-and-transition-graph-safety", "Verus-proves-the-written-phase-aware-carrier-under-an-exact-average-precondition", "CONVERGED-is-a-state-label-not-a-liveness-theorem"},
     validCases |-> {"peak-cooling-converged"},
     boundaryCases |-> {"awakened-reactivation"},
     misuseCases |-> {"incorrect-post-slide-average"},
     failureCases |-> {"torn-phase-history-state"},
     globalAssumptions |-> GlobalModelingAssumptionNames,
     conformanceConditions |-> ConformanceConditions,
     applicableFamilies |-> {"obligation", "check-act", "ownership-assurance", "refinement"},
     dischargedFamilies |-> {"obligation", "check-act", "ownership-assurance", "refinement"},
     transferClasses |-> {"safety"},
     refinementStatus |-> "mechanized",
     witnessStates |-> {"active-cold", "cooling", "converged", "invalid-transition"},
     witnessInitial |-> {"active-cold"},
     witnessObligationStates |-> {"active-cold", "cooling", "converged"},
     witnessViolationStates |-> {"invalid-transition"},
     witnessSystemSteps |-> {<<"active-cold", "cooling">>, <<"cooling", "converged">>, <<"converged", "converged">>},
     witnessEnvironmentSteps |-> {},
     witnessActionSteps |-> WitnessActionSteps,
     witnessRelySteps |-> {},
     witnessCommitSteps |-> {<<"active-cold", "cooling">>, <<"cooling", "converged">>, <<"converged", "converged">>},
     witnessFailureSteps |-> {},
     witnessInterferenceSteps |-> {},
     witnessCheckActMode |-> "atomic",
     witnessCheckResultStates |-> {"active-cold", "cooling", "converged"},
     witnessPredicateStates |-> {"active-cold", "cooling", "converged"},
     witnessActors |-> {"governor-claimant", "governor-authority", "delta-provider"},
     witnessProviders |-> {"governor-authority", "delta-provider"},
     witnessClaimant |-> "governor-claimant",
     witnessCommitOwner |-> "governor-authority",
     witnessCommitDelegate |-> "governor-authority",
     witnessAssuranceProvider |-> "governor-authority",
     witnessAssurancePosition |-> "at-commit",
     witnessPreventionControllers |-> {"governor-authority"},
     witnessUnavailableProviders |-> {},
     witnessPersistentObserve |-> WitnessPersistentObserve,
     witnessPersistentEvidence |-> TRUE,
     witnessRecoveryAvailable |-> FALSE,
     witnessActiveStates |-> {"active-cold", "cooling", "converged"},
     witnessClosedStates |-> {},
     witnessProgressSteps |-> {},
     witnessOtherSteps |-> {},
     witnessHandoffSteps |-> {},
     witnessRankBound |-> 0,
     witnessRank |-> WitnessRank,
     witnessFairnessOwners |-> {"governor-authority"},
     witnessFairnessOwner |-> "governor-authority",
     witnessFairnessOwnerOf |-> WitnessFairnessOwnerOf]

====
