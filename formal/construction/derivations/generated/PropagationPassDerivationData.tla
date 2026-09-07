---- MODULE PropagationPassDerivationData ----
EXTENDS StructureDerivationSchema

\* Generated from the checked derivation record. Do not edit by hand.

ImplementationStateMap ==
    [key \in {"values", "snapshot", "updated", "iteration", "changed", "round"} |->
        CASE key = "values" -> "values"
          [] key = "snapshot" -> "snapshot"
          [] key = "updated" -> "updated"
          [] key = "iteration" -> "iteration"
          [] key = "changed" -> "changed"
          [] key = "round" -> "round"
          [] OTHER -> "round"]

ObservationMap ==
    [key \in {"values", "snapshot", "updated", "iteration", "changed", "round"} |->
        CASE key = "values" -> "values"
          [] key = "snapshot" -> "snapshot"
          [] key = "updated" -> "updated"
          [] key = "iteration" -> "iteration"
          [] key = "changed" -> "changed"
          [] key = "round" -> "round"
          [] OTHER -> "round"]

ActionMap ==
    [key \in {"StartRound", "UpdateNode", "EndRound", "Terminate"} |->
        CASE key = "StartRound" -> {"start_round"}
          [] key = "UpdateNode" -> {"update_node"}
          [] key = "EndRound" -> {"end_round"}
          [] key = "Terminate" -> {"terminate"}
          [] OTHER -> {"terminate"}]

ViolationOf ==
    [key \in {"IterationBound", "SnapshotLocality", "EventualSettledOrIterationLimit"} |->
        CASE key = "IterationBound" -> "IterationLimitExceeded"
          [] key = "SnapshotLocality" -> "LiveValueReadDuringRound"
          [] key = "EventualSettledOrIterationLimit" -> "InfiniteEnabledNonclosure"
          [] OTHER -> "InfiniteEnabledNonclosure"]

OwnerOf ==
    [key \in {"StartRound", "UpdateNode", "EndRound", "Terminate"} |->
        CASE key = "StartRound" -> "propagation-executor"
          [] key = "UpdateNode" -> "propagation-executor"
          [] key = "EndRound" -> "propagation-executor"
          [] key = "Terminate" -> "propagation-executor"
          [] OTHER -> "propagation-executor"]

DelegateOf ==
    [key \in {"StartRound", "UpdateNode", "EndRound", "Terminate"} |->
        CASE key = "StartRound" -> {"propagation-executor"}
          [] key = "UpdateNode" -> {"propagation-executor"}
          [] key = "EndRound" -> {"propagation-executor"}
          [] key = "Terminate" -> {"propagation-executor"}
          [] OTHER -> {"propagation-executor"}]

AssuranceAt ==
    [key \in {"StartRound", "UpdateNode", "EndRound"} |->
        CASE key = "StartRound" -> "at-commit"
          [] key = "UpdateNode" -> "at-commit"
          [] key = "EndRound" -> "at-commit"
          [] OTHER -> "at-commit"]

WitnessPersistentObserve ==
    [key \in {"idle", "running", "updated", "closed", "violating"} |->
        CASE key = "idle" -> TRUE
          [] key = "running" -> TRUE
          [] key = "updated" -> TRUE
          [] key = "closed" -> TRUE
          [] key = "violating" -> FALSE
          [] OTHER -> FALSE]

WitnessRank ==
    [key \in {"idle", "running", "updated", "closed", "violating"} |->
        CASE key = "idle" -> 3
          [] key = "running" -> 2
          [] key = "updated" -> 1
          [] key = "closed" -> 0
          [] key = "violating" -> 0
          [] OTHER -> 0]

WitnessFairnessOwnerOf ==
    [key \in {<<"idle", "running">>, <<"running", "updated">>, <<"updated", "closed">>} |->
        CASE key = <<"idle", "running">> -> "workflow-scheduler"
          [] key = <<"running", "updated">> -> "workflow-scheduler"
          [] key = <<"updated", "closed">> -> "workflow-scheduler"
          [] OTHER -> "workflow-scheduler"]

WitnessActionSteps ==
    [key \in {"StartRound", "UpdateNode", "EndRound", "Terminate"} |->
        CASE key = "StartRound" -> {<<"idle", "running">>}
          [] key = "UpdateNode" -> {<<"running", "updated">>}
          [] key = "EndRound" -> {<<"updated", "closed">>}
          [] key = "Terminate" -> {<<"closed", "closed">>}
          [] OTHER -> {<<"closed", "closed">>}]

Derivation ==
    [structure |-> "PropagationPass",
     kind |-> "abstraction-primitive",
     propertyClasses |-> {"safety", "liveness"},
     stateFields |-> {"values", "snapshot", "updated", "iteration", "changed", "round"},
     observationFields |-> {"values", "snapshot", "updated", "iteration", "changed", "round"},
     implementationStateFields |-> {"values", "snapshot", "updated", "iteration", "changed", "round"},
     implementationStateMap |-> ImplementationStateMap,
     observationMap |-> ObservationMap,
     canonicalActions |-> {"StartRound", "UpdateNode", "EndRound", "Terminate"},
     systemActions |-> {"StartRound", "UpdateNode", "EndRound", "Terminate"},
     environmentActions |-> {},
     failureActions |-> {},
     commitActions |-> {"StartRound", "UpdateNode", "EndRound"},
     executableActions |-> {"start_round", "update_node", "end_round", "terminate"},
     actionMap |-> ActionMap,
     obligations |-> {"IterationBound", "SnapshotLocality", "EventualSettledOrIterationLimit"},
     violations |-> {"IterationLimitExceeded", "LiveValueReadDuringRound", "InfiniteEnabledNonclosure"},
     violationOf |-> ViolationOf,
     actors |-> {"propagation-claimant", "propagation-executor", "workflow-scheduler"},
     claimant |-> "propagation-claimant",
     ownerOf |-> OwnerOf,
     delegateOf |-> DelegateOf,
     assuranceAt |-> AssuranceAt,
     relies |-> {"finite-node-universe", "weak-fair-round-admission", "weak-fair-each-node-update", "weak-fair-round-closure", "serialized-round-state-mutation"},
     guarantees |-> {"propagationpass-written-profile-refinement", "bounded-snapshot-rounds", "eventual-settlement-or-limit", "propagation-owner-ceiling", "propagation-executable-transfer"},
     runtimeProviders |-> {"propagation-executor", "workflow-scheduler", "exclusive-round-state-provider"},
     failureCeilings |-> {"no-modeled-executor-crash-or-state-loss", "no-wall-clock-or-step-bound", "no-progress-without-the-named-weak-fair-scheduler", "finite-node-universe-only"},
     executionCarriers |-> {"Sequential"},
     localTheorems |-> {"PropagationPassImplRefinesSpec_Proof!RefinementThm", "PropagationPassGraph_Proof!IterationBoundSafety", "PropagationPassGraph_Proof!SnapshotLocalitySafety", "PropagationPassGraph_Proof!EventualSettledOrIterationLimitProved", "TheoryKernel_Proof!ObligationPreservation", "ProgressKernel_Proof!RankedProgress", "OwnershipAssuranceKernel_Proof!OwnershipAssuranceClassification"},
     executablePointers |-> {"formal/structures/PropagationPass/refinement/PropagationPassImplRefinesSpec.tla", "formal/structures/PropagationPass/refinement/PropagationPassImplRefinesSpec_Proof.tla", "crate://automation-structures/0.2.3/src/primitives/propagation_pass.rs", "formal/structures/PropagationPass/PropagationPassGraph.tla", "formal/structures/PropagationPass/PropagationPassGraph_Proof.tla"},
     libraryPremises |-> {"PropagationPass-written-contract-refinement-profile", "canonical-snapshot-round-machine", "IterationBoundSafety", "SnapshotLocalitySafety", "EventualSettledOrIterationLimitProved", "ObligationPreservation", "RankedProgress", "OwnershipAssuranceClassification"},
     deploymentPremises |-> {"MaxIterationsType", "MaxValueType", "NodesFinite", "weak-fair-round-admission", "weak-fair-each-node-update", "weak-fair-round-closure", "serialized-round-state-mutation", "complete-transition-tcb-with-no-live-value-bypass"},
     residuals |-> {"formal-correspondence-is-limited-to-the-written-state-action-and-premise-map", "Combine-is-domain-supplied-and-no-universal-convergence-result-follows", "the-local-temporal-result-is-eventual-closure-not-a-deadline", "Rust-contract-verification-does-not-prove-runtime-scheduler-fairness", "no-crash-retry-or-persistent-round-recovery-model"},
     evidenceCeilings |-> {"implementation-refinement-covers-only-the-written-bounded-contract-profile", "TLAPS-proves-the-local-temporal-theorem-under-finite-Nodes-and-explicit-weak-fairness", "TLC-bounds-only-the-configured-three-node-path", "Verus-proves-action-contracts-but-not-infinite-trace-fairness", "executable-liveness-transfer-requires-the-same-written-fairness-owner"},
     validCases |-> {"complete-snapshot-round", "fair-eventual-closure"},
     boundaryCases |-> {"unchanged-round-settles", "iteration-ceiling"},
     misuseCases |-> {"live-value-combine", "safety-only-progress-surrogate"},
     failureCases |-> {"fairness-provider-absent", "round-state-loss"},
     globalAssumptions |-> GlobalModelingAssumptionNames,
     conformanceConditions |-> ConformanceConditions,
     applicableFamilies |-> {"obligation", "progress", "ownership-assurance", "refinement"},
     dischargedFamilies |-> {"obligation", "progress", "ownership-assurance", "refinement"},
     transferClasses |-> {"safety", "liveness"},
     refinementStatus |-> "mechanized",
     witnessStates |-> {"idle", "running", "updated", "closed", "violating"},
     witnessInitial |-> {"idle"},
     witnessObligationStates |-> {"idle", "running", "updated", "closed"},
     witnessViolationStates |-> {"violating"},
     witnessSystemSteps |-> {<<"idle", "running">>, <<"running", "updated">>, <<"updated", "closed">>, <<"closed", "closed">>},
     witnessEnvironmentSteps |-> {},
     witnessActionSteps |-> WitnessActionSteps,
     witnessRelySteps |-> {},
     witnessCommitSteps |-> {<<"idle", "running">>, <<"running", "updated">>, <<"updated", "closed">>},
     witnessFailureSteps |-> {},
     witnessInterferenceSteps |-> {},
     witnessCheckActMode |-> "atomic",
     witnessCheckResultStates |-> {},
     witnessPredicateStates |-> {},
     witnessActors |-> {"propagation-claimant", "propagation-executor", "workflow-scheduler"},
     witnessProviders |-> {"propagation-executor", "workflow-scheduler"},
     witnessClaimant |-> "propagation-claimant",
     witnessCommitOwner |-> "propagation-executor",
     witnessCommitDelegate |-> "propagation-executor",
     witnessAssuranceProvider |-> "propagation-executor",
     witnessAssurancePosition |-> "at-commit",
     witnessPreventionControllers |-> {"propagation-executor"},
     witnessUnavailableProviders |-> {},
     witnessPersistentObserve |-> WitnessPersistentObserve,
     witnessPersistentEvidence |-> TRUE,
     witnessRecoveryAvailable |-> FALSE,
     witnessActiveStates |-> {"idle", "running", "updated"},
     witnessClosedStates |-> {"closed", "violating"},
     witnessProgressSteps |-> {<<"idle", "running">>, <<"running", "updated">>, <<"updated", "closed">>},
     witnessOtherSteps |-> {<<"closed", "closed">>, <<"violating", "violating">>},
     witnessHandoffSteps |-> {<<"idle", "running">>},
     witnessRankBound |-> 3,
     witnessRank |-> WitnessRank,
     witnessFairnessOwners |-> {"workflow-scheduler"},
     witnessFairnessOwner |-> "workflow-scheduler",
     witnessFairnessOwnerOf |-> WitnessFairnessOwnerOf]

====
