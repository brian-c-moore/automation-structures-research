---- MODULE RateLimitDerivationData ----
EXTENDS StructureDerivationSchema

\* Generated from the checked derivation record. Do not edit by hand.

ImplementationStateMap ==
    [key \in {"count", "window_start", "clock"} |->
        CASE key = "count" -> "count"
          [] key = "window_start" -> "window_start"
          [] key = "clock" -> "clock"
          [] OTHER -> "clock"]

ObservationMap ==
    [key \in {"count", "window_start", "clock"} |->
        CASE key = "count" -> "count"
          [] key = "window_start" -> "window_start"
          [] key = "clock" -> "clock"
          [] OTHER -> "clock"]

ActionMap ==
    [key \in {"TryAcquire", "Tick"} |->
        CASE key = "TryAcquire" -> {"try_acquire"}
          [] key = "Tick" -> {"tick"}
          [] OTHER -> {"tick"}]

ViolationOf ==
    [key \in {"WindowCountBound", "WindowStartNotFuture"} |->
        CASE key = "WindowCountBound" -> "WindowLimitExceeded"
          [] key = "WindowStartNotFuture" -> "FutureWindowStart"
          [] OTHER -> "FutureWindowStart"]

OwnerOf ==
    [key \in {"TryAcquire", "Tick"} |->
        CASE key = "TryAcquire" -> "rate-authority"
          [] key = "Tick" -> "clock-provider"
          [] OTHER -> "clock-provider"]

DelegateOf ==
    [key \in {"TryAcquire", "Tick"} |->
        CASE key = "TryAcquire" -> {"rate-authority"}
          [] key = "Tick" -> {"clock-provider"}
          [] OTHER -> {"clock-provider"}]

AssuranceAt ==
    [key \in {"TryAcquire"} |->
        CASE key = "TryAcquire" -> "at-commit"
          [] OTHER -> "at-commit"]

WitnessPersistentObserve ==
    [key \in {"empty-window", "counted-window", "over-limit"} |->
        CASE key = "empty-window" -> TRUE
          [] key = "counted-window" -> TRUE
          [] key = "over-limit" -> FALSE
          [] OTHER -> FALSE]

WitnessRank ==
    [key \in {"empty-window", "counted-window", "over-limit"} |->
        CASE key = "empty-window" -> 0
          [] key = "counted-window" -> 0
          [] key = "over-limit" -> 0
          [] OTHER -> 0]

WitnessFairnessOwnerOf == [key \in {} |-> "unused"]

WitnessActionSteps ==
    [key \in {"TryAcquire", "Tick"} |->
        CASE key = "TryAcquire" -> {<<"empty-window", "counted-window">>}
          [] key = "Tick" -> {<<"counted-window", "empty-window">>}
          [] OTHER -> {<<"counted-window", "empty-window">>}]

Derivation ==
    [structure |-> "RateLimit",
     kind |-> "named-composition",
     propertyClasses |-> {"safety"},
     stateFields |-> {"count", "window_start", "clock"},
     observationFields |-> {"count", "window_start", "clock"},
     implementationStateFields |-> {"count", "window_start", "clock"},
     implementationStateMap |-> ImplementationStateMap,
     observationMap |-> ObservationMap,
     canonicalActions |-> {"TryAcquire", "Tick"},
     systemActions |-> {"TryAcquire"},
     environmentActions |-> {"Tick"},
     failureActions |-> {},
     commitActions |-> {"TryAcquire"},
     executableActions |-> {"try_acquire", "tick"},
     actionMap |-> ActionMap,
     obligations |-> {"WindowCountBound", "WindowStartNotFuture"},
     violations |-> {"WindowLimitExceeded", "FutureWindowStart"},
     violationOf |-> ViolationOf,
     actors |-> {"rate-claimant", "rate-authority", "clock-provider"},
     claimant |-> "rate-claimant",
     ownerOf |-> OwnerOf,
     delegateOf |-> DelegateOf,
     assuranceAt |-> AssuranceAt,
     relies |-> {"monotone-bounded-clock-delivery", "serialized-rate-state-mutation", "atomic-window-guard-and-count-update"},
     guarantees |-> {"ratelimit-written-profile-refinement", "window-count-bound", "atomic-acquire-license", "clock-owner-ceiling"},
     runtimeProviders |-> {"rate-authority", "clock-provider", "exclusive-mutation-provider"},
     failureCeilings |-> {"clock-regression-outside-rely", "no-modeled-crash-or-durable-window", "concurrent-bypass-acquire-outside-boundary"},
     executionCarriers |-> {"Sequential"},
     localTheorems |-> {"RateLimitImplRefinesSpec_Proof!RefinementThm", "RateLimit_Proof!Safety", "RateLimit_Proof!WindowCountBoundSafety", "RateLimit_Proof!WindowStartNotFutureSafety", "TheoryKernel_Proof!ObligationPreservation", "TheoryKernel_Proof!CheckActStability", "OwnershipAssuranceKernel_Proof!OwnershipAssuranceClassification"},
     executablePointers |-> {"formal/structures/RateLimit/refinement/RateLimitImplRefinesSpec.tla", "formal/structures/RateLimit/refinement/RateLimitImplRefinesSpec_Proof.tla", "crate://automation-structures/0.2.3/src/compositions/rate_limit.rs", "formal/structures/RateLimit/RateLimit.tla", "formal/structures/RateLimit/RateLimit_Proof.tla"},
     libraryPremises |-> {"RateLimit-written-contract-refinement-profile", "canonical-window-machine", "RateLimit-Safety", "ObligationPreservation", "CheckActStability", "OwnershipAssuranceClassification"},
     deploymentPremises |-> {"MaxPerWindowType", "WindowDurationType", "MaxClockType", "monotone-bounded-clock-delivery", "serialized-rate-state-mutation", "atomic-window-guard-and-count-update"},
     residuals |-> {"formal-correspondence-is-limited-to-the-written-state-action-and-premise-map", "no-wall-clock-accuracy-result", "no-distributed-rate-limit-protocol", "no-throughput-or-fairness-guarantee"},
     evidenceCeilings |-> {"implementation-refinement-covers-only-the-written-bounded-contract-profile", "TLAPS-proves-the-bounded-logical-clock-machine", "Verus-proves-the-written-u64-state-contract", "KAT-clock-boundaries-do-not-prove-real-clock-delivery"},
     validCases |-> {"acquire-below-limit"},
     boundaryCases |-> {"window-rollover"},
     misuseCases |-> {"regressing-clock"},
     failureCases |-> {"split-window-commit"},
     globalAssumptions |-> GlobalModelingAssumptionNames,
     conformanceConditions |-> ConformanceConditions,
     applicableFamilies |-> {"obligation", "check-act", "ownership-assurance", "refinement"},
     dischargedFamilies |-> {"obligation", "check-act", "ownership-assurance", "refinement"},
     transferClasses |-> {"safety"},
     refinementStatus |-> "mechanized",
     witnessStates |-> {"empty-window", "counted-window", "over-limit"},
     witnessInitial |-> {"empty-window"},
     witnessObligationStates |-> {"empty-window", "counted-window"},
     witnessViolationStates |-> {"over-limit"},
     witnessSystemSteps |-> {<<"empty-window", "counted-window">>},
     witnessEnvironmentSteps |-> {<<"counted-window", "empty-window">>},
     witnessActionSteps |-> WitnessActionSteps,
     witnessRelySteps |-> {<<"counted-window", "empty-window">>},
     witnessCommitSteps |-> {<<"empty-window", "counted-window">>},
     witnessFailureSteps |-> {},
     witnessInterferenceSteps |-> {},
     witnessCheckActMode |-> "atomic",
     witnessCheckResultStates |-> {"empty-window", "counted-window"},
     witnessPredicateStates |-> {"empty-window", "counted-window"},
     witnessActors |-> {"rate-claimant", "rate-authority", "clock-provider"},
     witnessProviders |-> {"rate-authority", "clock-provider"},
     witnessClaimant |-> "rate-claimant",
     witnessCommitOwner |-> "rate-authority",
     witnessCommitDelegate |-> "rate-authority",
     witnessAssuranceProvider |-> "rate-authority",
     witnessAssurancePosition |-> "at-commit",
     witnessPreventionControllers |-> {"rate-authority"},
     witnessUnavailableProviders |-> {},
     witnessPersistentObserve |-> WitnessPersistentObserve,
     witnessPersistentEvidence |-> TRUE,
     witnessRecoveryAvailable |-> FALSE,
     witnessActiveStates |-> {"empty-window", "counted-window"},
     witnessClosedStates |-> {},
     witnessProgressSteps |-> {},
     witnessOtherSteps |-> {},
     witnessHandoffSteps |-> {},
     witnessRankBound |-> 0,
     witnessRank |-> WitnessRank,
     witnessFairnessOwners |-> {"rate-authority"},
     witnessFairnessOwner |-> "rate-authority",
     witnessFairnessOwnerOf |-> WitnessFairnessOwnerOf]

====
