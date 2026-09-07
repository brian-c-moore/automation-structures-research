---- MODULE SignalDerivationData ----
EXTENDS StructureDerivationSchema

\* Generated from the checked derivation record. Do not edit by hand.

ImplementationStateMap ==
    [key \in {"current_value", "change_observed", "pending_notifications", "notified"} |->
        CASE key = "current_value" -> "current_value"
          [] key = "change_observed" -> "change_observed"
          [] key = "pending_notifications" -> "pending_notifications"
          [] key = "notified" -> "notified"
          [] OTHER -> "notified"]

ObservationMap ==
    [key \in {"current_value", "change_observed", "pending_notifications", "notified"} |->
        CASE key = "current_value" -> "current_value"
          [] key = "change_observed" -> "change_observed"
          [] key = "pending_notifications" -> "pending_notifications"
          [] key = "notified" -> "notified"
          [] OTHER -> "notified"]

ActionMap ==
    [key \in {"SetValue", "NotifyListener"} |->
        CASE key = "SetValue" -> {"set_value"}
          [] key = "NotifyListener" -> {"notify_listener"}
          [] OTHER -> {"notify_listener"}]

ViolationOf ==
    [key \in {"PendingNotifiedDisjointness", "NotificationProvenance"} |->
        CASE key = "PendingNotifiedDisjointness" -> "PendingNotifiedOverlap"
          [] key = "NotificationProvenance" -> "NotificationWithoutChange"
          [] OTHER -> "NotificationWithoutChange"]

OwnerOf ==
    [key \in {"SetValue", "NotifyListener"} |->
        CASE key = "SetValue" -> "signal-authority"
          [] key = "NotifyListener" -> "signal-authority"
          [] OTHER -> "signal-authority"]

DelegateOf ==
    [key \in {"SetValue", "NotifyListener"} |->
        CASE key = "SetValue" -> {"signal-authority"}
          [] key = "NotifyListener" -> {"signal-authority"}
          [] OTHER -> {"signal-authority"}]

AssuranceAt ==
    [key \in {"SetValue", "NotifyListener"} |->
        CASE key = "SetValue" -> "at-commit"
          [] key = "NotifyListener" -> "at-commit"
          [] OTHER -> "at-commit"]

WitnessPersistentObserve ==
    [key \in {"idle", "pending", "inconsistent-delivery"} |->
        CASE key = "idle" -> TRUE
          [] key = "pending" -> TRUE
          [] key = "inconsistent-delivery" -> FALSE
          [] OTHER -> FALSE]

WitnessRank ==
    [key \in {"idle", "pending", "inconsistent-delivery"} |->
        CASE key = "idle" -> 0
          [] key = "pending" -> 0
          [] key = "inconsistent-delivery" -> 0
          [] OTHER -> 0]

WitnessFairnessOwnerOf == [key \in {} |-> "unused"]

WitnessActionSteps ==
    [key \in {"SetValue", "NotifyListener"} |->
        CASE key = "SetValue" -> {<<"idle", "pending">>}
          [] key = "NotifyListener" -> {<<"pending", "idle">>}
          [] OTHER -> {<<"pending", "idle">>}]

Derivation ==
    [structure |-> "Signal",
     kind |-> "named-composition",
     propertyClasses |-> {"safety"},
     stateFields |-> {"current_value", "change_observed", "pending_notifications", "notified"},
     observationFields |-> {"current_value", "change_observed", "pending_notifications", "notified"},
     implementationStateFields |-> {"current_value", "change_observed", "pending_notifications", "notified"},
     implementationStateMap |-> ImplementationStateMap,
     observationMap |-> ObservationMap,
     canonicalActions |-> {"SetValue", "NotifyListener"},
     systemActions |-> {"SetValue", "NotifyListener"},
     environmentActions |-> {},
     failureActions |-> {},
     commitActions |-> {"SetValue", "NotifyListener"},
     executableActions |-> {"set_value", "notify_listener"},
     actionMap |-> ActionMap,
     obligations |-> {"PendingNotifiedDisjointness", "NotificationProvenance"},
     violations |-> {"PendingNotifiedOverlap", "NotificationWithoutChange"},
     violationOf |-> ViolationOf,
     actors |-> {"signal-claimant", "signal-authority", "listener"},
     claimant |-> "signal-claimant",
     ownerOf |-> OwnerOf,
     delegateOf |-> DelegateOf,
     assuranceAt |-> AssuranceAt,
     relies |-> {"finite-value-and-listener-domains", "serialized-signal-state-mutation", "atomic-pending-notified-partition-update"},
     guarantees |-> {"signal-written-profile-refinement", "signal-notification-safety", "signal-atomic-partition", "signal-owner-ceiling"},
     runtimeProviders |-> {"signal-authority", "listener-index-provider", "exclusive-mutation-provider"},
     failureCeilings |-> {"no-modeled-crash-or-durable-delivery", "concurrent-bypass-writer-outside-boundary", "no-listener-failure-or-retry-state"},
     executionCarriers |-> {"Sequential"},
     localTheorems |-> {"SignalImplRefinesSpec_Proof!RefinementThm", "Signal_Proof!Safety", "Signal_Proof!PendingNotifiedDisjointnessSafety", "Signal_Proof!NotificationProvenanceSafety", "TheoryKernel_Proof!ObligationPreservation", "TheoryKernel_Proof!CheckActStability", "OwnershipAssuranceKernel_Proof!OwnershipAssuranceClassification"},
     executablePointers |-> {"formal/structures/Signal/refinement/SignalImplRefinesSpec.tla", "formal/structures/Signal/refinement/SignalImplRefinesSpec_Proof.tla", "crate://automation-structures/0.2.3/src/compositions/signal.rs", "formal/structures/Signal/Signal.tla", "formal/structures/Signal/Signal_Proof.tla"},
     libraryPremises |-> {"Signal-written-contract-refinement-profile", "canonical-signal-machine", "Signal-Safety", "ObligationPreservation", "CheckActStability", "OwnershipAssuranceClassification"},
     deploymentPremises |-> {"finite-value-and-listener-domains", "serialized-signal-state-mutation", "atomic-pending-notified-partition-update", "complete-signal-writer-inventory"},
     residuals |-> {"formal-correspondence-is-limited-to-the-written-state-action-and-premise-map", "no-eventual-notification-result", "no-exactly-once-delivery-result", "no-durable-or-distributed-signal-protocol"},
     evidenceCeilings |-> {"implementation-refinement-covers-only-the-written-bounded-contract-profile", "TLAPS-proves-delivery-set-safety-and-provenance", "Verus-proves-the-written-finite-listener-representation", "no-fairness-or-delivery-latency-result"},
     validCases |-> {"change-then-notify"},
     boundaryCases |-> {"same-value-stutter"},
     misuseCases |-> {"notify-nonpending-listener"},
     failureCases |-> {"split-pending-notified-update"},
     globalAssumptions |-> GlobalModelingAssumptionNames,
     conformanceConditions |-> ConformanceConditions,
     applicableFamilies |-> {"obligation", "check-act", "ownership-assurance", "refinement"},
     dischargedFamilies |-> {"obligation", "check-act", "ownership-assurance", "refinement"},
     transferClasses |-> {"safety"},
     refinementStatus |-> "mechanized",
     witnessStates |-> {"idle", "pending", "inconsistent-delivery"},
     witnessInitial |-> {"idle"},
     witnessObligationStates |-> {"idle", "pending"},
     witnessViolationStates |-> {"inconsistent-delivery"},
     witnessSystemSteps |-> {<<"idle", "pending">>, <<"pending", "idle">>},
     witnessEnvironmentSteps |-> {},
     witnessActionSteps |-> WitnessActionSteps,
     witnessRelySteps |-> {},
     witnessCommitSteps |-> {<<"idle", "pending">>, <<"pending", "idle">>},
     witnessFailureSteps |-> {},
     witnessInterferenceSteps |-> {},
     witnessCheckActMode |-> "atomic",
     witnessCheckResultStates |-> {"idle", "pending"},
     witnessPredicateStates |-> {"idle", "pending"},
     witnessActors |-> {"signal-claimant", "signal-authority", "listener"},
     witnessProviders |-> {"signal-authority"},
     witnessClaimant |-> "signal-claimant",
     witnessCommitOwner |-> "signal-authority",
     witnessCommitDelegate |-> "signal-authority",
     witnessAssuranceProvider |-> "signal-authority",
     witnessAssurancePosition |-> "at-commit",
     witnessPreventionControllers |-> {"signal-authority"},
     witnessUnavailableProviders |-> {},
     witnessPersistentObserve |-> WitnessPersistentObserve,
     witnessPersistentEvidence |-> TRUE,
     witnessRecoveryAvailable |-> FALSE,
     witnessActiveStates |-> {"idle", "pending"},
     witnessClosedStates |-> {},
     witnessProgressSteps |-> {},
     witnessOtherSteps |-> {},
     witnessHandoffSteps |-> {},
     witnessRankBound |-> 0,
     witnessRank |-> WitnessRank,
     witnessFairnessOwners |-> {"signal-authority"},
     witnessFairnessOwner |-> "signal-authority",
     witnessFairnessOwnerOf |-> WitnessFairnessOwnerOf]

====
