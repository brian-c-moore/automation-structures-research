---- MODULE SequentialDerivationData ----
EXTENDS StructureDerivationSchema

\* Generated from the checked derivation record. Do not edit by hand.

ImplementationStateMap ==
    [key \in {"pc", "value", "active", "history"} |->
        CASE key = "pc" -> "pc"
          [] key = "value" -> "value"
          [] key = "active" -> "active"
          [] key = "history" -> "history"
          [] OTHER -> "history"]

ObservationMap ==
    [key \in {"pc", "value", "active", "history"} |->
        CASE key = "pc" -> "pc"
          [] key = "value" -> "value"
          [] key = "active" -> "active"
          [] key = "history" -> "history"
          [] OTHER -> "history"]

ActionMap ==
    [key \in {"BeginStep", "CompleteStep", "DoneStuttering"} |->
        CASE key = "BeginStep" -> {"begin_step"}
          [] key = "CompleteStep" -> {"complete_step"}
          [] key = "DoneStuttering" -> {"done_stuttering"}
          [] OTHER -> {"done_stuttering"}]

ViolationOf ==
    [key \in {"TypeInvariant", "HistoryPositionAgreement"} |->
        CASE key = "TypeInvariant" -> "CarrierTypeViolation"
          [] key = "HistoryPositionAgreement" -> "HistoryCursorMismatch"
          [] OTHER -> "HistoryCursorMismatch"]

OwnerOf ==
    [key \in {"BeginStep", "CompleteStep", "DoneStuttering"} |->
        CASE key = "BeginStep" -> "sequential-executor"
          [] key = "CompleteStep" -> "sequential-executor"
          [] key = "DoneStuttering" -> "sequential-executor"
          [] OTHER -> "sequential-executor"]

DelegateOf ==
    [key \in {"BeginStep", "CompleteStep", "DoneStuttering"} |->
        CASE key = "BeginStep" -> {"sequential-executor"}
          [] key = "CompleteStep" -> {"sequential-executor"}
          [] key = "DoneStuttering" -> {"sequential-executor"}
          [] OTHER -> {"sequential-executor"}]

AssuranceAt ==
    [key \in {"BeginStep", "CompleteStep"} |->
        CASE key = "BeginStep" -> "at-commit"
          [] key = "CompleteStep" -> "at-commit"
          [] OTHER -> "at-commit"]

WitnessPersistentObserve ==
    [key \in {"idle-0", "active-0", "idle-1", "active-1", "done", "bad-history"} |->
        CASE key = "idle-0" -> TRUE
          [] key = "active-0" -> TRUE
          [] key = "idle-1" -> TRUE
          [] key = "active-1" -> TRUE
          [] key = "done" -> TRUE
          [] key = "bad-history" -> FALSE
          [] OTHER -> FALSE]

WitnessRank ==
    [key \in {"idle-0", "active-0", "idle-1", "active-1", "done", "bad-history"} |->
        CASE key = "idle-0" -> 4
          [] key = "active-0" -> 3
          [] key = "idle-1" -> 2
          [] key = "active-1" -> 1
          [] key = "done" -> 0
          [] key = "bad-history" -> 0
          [] OTHER -> 0]

WitnessFairnessOwnerOf == [key \in {} |-> "unused"]

WitnessActionSteps ==
    [key \in {"BeginStep", "CompleteStep", "DoneStuttering"} |->
        CASE key = "BeginStep" -> {<<"idle-0", "active-0">>, <<"idle-1", "active-1">>}
          [] key = "CompleteStep" -> {<<"active-0", "idle-1">>, <<"active-1", "done">>}
          [] key = "DoneStuttering" -> {<<"done", "done">>}
          [] OTHER -> {<<"done", "done">>}]

Derivation ==
    [structure |-> "Sequential",
     kind |-> "execution-modality",
     propertyClasses |-> {"safety"},
     stateFields |-> {"pc", "value", "active", "history"},
     observationFields |-> {"pc", "value", "active", "history"},
     implementationStateFields |-> {"pc", "value", "active", "history"},
     implementationStateMap |-> ImplementationStateMap,
     observationMap |-> ObservationMap,
     canonicalActions |-> {"BeginStep", "CompleteStep", "DoneStuttering"},
     systemActions |-> {"BeginStep", "CompleteStep", "DoneStuttering"},
     environmentActions |-> {},
     failureActions |-> {},
     commitActions |-> {"BeginStep", "CompleteStep"},
     executableActions |-> {"begin_step", "complete_step", "done_stuttering"},
     actionMap |-> ActionMap,
     obligations |-> {"TypeInvariant", "HistoryPositionAgreement"},
     violations |-> {"CarrierTypeViolation", "HistoryCursorMismatch"},
     violationOf |-> ViolationOf,
     actors |-> {"workflow-claimant", "sequential-executor"},
     claimant |-> "workflow-claimant",
     ownerOf |-> OwnerOf,
     delegateOf |-> DelegateOf,
     assuranceAt |-> AssuranceAt,
     relies |-> {"one-visible-logical-active-locus", "serialized-carrier-state-mutation", "positive-finite-step-count", "nonempty-finite-value-domain", "complete-carrier-writer-tcb"},
     guarantees |-> {"ordered-cursor-history", "typed-single-locus-state", "sequential-owner-ceiling", "sequential-executable-transfer"},
     runtimeProviders |-> {"sequential-executor", "value-provider", "carrier-state-provider"},
     failureCeilings |-> {"no-modeled-executor-crash-retry-or-persistent-recovery", "nested-or-hidden-concurrency-below-the-visible-step-boundary-is-not-excluded", "no-external-effect-ownership-or-success-result", "no-eventual-completion-or-time-bound"},
     executionCarriers |-> {"Sequential"},
     localTheorems |-> {"Sequential_Proof!TypeSafety", "Sequential_Proof!HistoryPositionAgreementSafety", "SequentialImplRefinesSpec_Proof!RefinementThm", "TheoryKernel_Proof!ObligationPreservation", "OwnershipAssuranceKernel_Proof!OwnershipAssuranceClassification"},
     executablePointers |-> {"development-copy://automation-structures/0.3.2/src/modalities/sequential.rs", "formal/execution/carriers/Sequential.tla", "formal/execution/carriers/Sequential_Proof.tla", "formal/execution/carriers/refinement/Sequential/SequentialImplRefinesSpec.tla", "formal/execution/carriers/refinement/Sequential/SequentialImplRefinesSpec_Proof.tla", "formal/execution/refinements/SequentialRefinesStepGraph.tla", "formal/execution/refinements/SequentialRefinesStepGraph_Proof.tla"},
     libraryPremises |-> {"canonical-three-action-sequential-carrier", "TypeSafety", "HistoryPositionAgreementSafety", "ObligationPreservation", "OwnershipAssuranceClassification"},
     deploymentPremises |-> {"StepsType", "ValueDomainNonEmpty", "finite-u64-value-domain-instantiation", "serialized-carrier-state-mutation", "one-visible-logical-active-locus", "complete-carrier-writer-tcb"},
     residuals |-> {"single-locus-is-a-declared-representation-ceiling-not-a-noninterference-theorem", "nested-runtime-concurrency-inside-one-visible-step-is-outside-the-carrier", "no-scheduler-fairness-eventual-completion-or-deadline", "no-crash-retry-idempotence-or-durable-history-result"},
     evidenceCeilings |-> {"TLAPS-proves-TypeInvariant-and-HistoryPositionAgreement-under-positive-Steps-and-nonempty-ValueDomain", "ActiveBeforeDone-is-an-inductive-strengthening-not-an-extra-advertised-claim", "Verus-proves-the-written-finite-u64-carrier-contracts", "existing-Sequential-to-StepGraph-refinement-is-relationship-evidence-not-the-six-record-bridge"},
     validCases |-> {"begin-complete-pair", "terminal-stutter"},
     boundaryCases |-> {"first-step", "out-of-domain-value-rejected"},
     misuseCases |-> {"double-begin", "cursor-without-history"},
     failureCases |-> {"crash-between-begin-and-complete", "hidden-parallel-effects"},
     globalAssumptions |-> GlobalModelingAssumptionNames,
     conformanceConditions |-> ConformanceConditions,
     applicableFamilies |-> {"obligation", "ownership-assurance", "refinement"},
     dischargedFamilies |-> {"obligation", "ownership-assurance", "refinement"},
     transferClasses |-> {"safety", "observation"},
     refinementStatus |-> "mechanized",
     witnessStates |-> {"idle-0", "active-0", "idle-1", "active-1", "done", "bad-history"},
     witnessInitial |-> {"idle-0"},
     witnessObligationStates |-> {"idle-0", "active-0", "idle-1", "active-1", "done"},
     witnessViolationStates |-> {"bad-history"},
     witnessSystemSteps |-> {<<"idle-0", "active-0">>, <<"active-0", "idle-1">>, <<"idle-1", "active-1">>, <<"active-1", "done">>, <<"done", "done">>},
     witnessEnvironmentSteps |-> {},
     witnessActionSteps |-> WitnessActionSteps,
     witnessRelySteps |-> {},
     witnessCommitSteps |-> {<<"idle-0", "active-0">>, <<"active-0", "idle-1">>, <<"idle-1", "active-1">>, <<"active-1", "done">>},
     witnessFailureSteps |-> {},
     witnessInterferenceSteps |-> {},
     witnessCheckActMode |-> "atomic",
     witnessCheckResultStates |-> {},
     witnessPredicateStates |-> {},
     witnessActors |-> {"workflow-claimant", "sequential-executor"},
     witnessProviders |-> {"sequential-executor"},
     witnessClaimant |-> "workflow-claimant",
     witnessCommitOwner |-> "sequential-executor",
     witnessCommitDelegate |-> "sequential-executor",
     witnessAssuranceProvider |-> "sequential-executor",
     witnessAssurancePosition |-> "at-commit",
     witnessPreventionControllers |-> {"sequential-executor"},
     witnessUnavailableProviders |-> {},
     witnessPersistentObserve |-> WitnessPersistentObserve,
     witnessPersistentEvidence |-> TRUE,
     witnessRecoveryAvailable |-> FALSE,
     witnessActiveStates |-> {"idle-0", "active-0", "idle-1", "active-1"},
     witnessClosedStates |-> {"done", "bad-history"},
     witnessProgressSteps |-> {<<"idle-0", "active-0">>, <<"active-0", "idle-1">>, <<"idle-1", "active-1">>, <<"active-1", "done">>},
     witnessOtherSteps |-> {<<"done", "done">>},
     witnessHandoffSteps |-> {<<"active-0", "idle-1">>, <<"active-1", "done">>},
     witnessRankBound |-> 4,
     witnessRank |-> WitnessRank,
     witnessFairnessOwners |-> {"sequential-executor"},
     witnessFairnessOwner |-> "sequential-executor",
     witnessFairnessOwnerOf |-> WitnessFairnessOwnerOf]

====
