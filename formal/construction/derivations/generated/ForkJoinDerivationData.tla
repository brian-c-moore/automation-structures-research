---- MODULE ForkJoinDerivationData ----
EXTENDS StructureDerivationSchema

\* Generated from the checked derivation record. Do not edit by hand.

ImplementationStateMap ==
    [key \in {"wstate", "wvalue", "phase", "output_ready", "output_snapshot"} |->
        CASE key = "wstate" -> "wstate"
          [] key = "wvalue" -> "wvalue"
          [] key = "phase" -> "phase"
          [] key = "output_ready" -> "output_ready"
          [] key = "output_snapshot" -> "output_snapshot"
          [] OTHER -> "output_snapshot"]

ObservationMap ==
    [key \in {"wstate", "wvalue", "phase", "output_ready", "output_snapshot"} |->
        CASE key = "wstate" -> "wstate"
          [] key = "wvalue" -> "wvalue"
          [] key = "phase" -> "phase"
          [] key = "output_ready" -> "output_ready"
          [] key = "output_snapshot" -> "output_snapshot"
          [] OTHER -> "output_snapshot"]

ActionMap ==
    [key \in {"StartWorker", "CompleteWorker", "Barrier", "ProduceOutput", "DoneStuttering"} |->
        CASE key = "StartWorker" -> {"start_worker"}
          [] key = "CompleteWorker" -> {"complete_worker"}
          [] key = "Barrier" -> {"barrier"}
          [] key = "ProduceOutput" -> {"produce_output"}
          [] key = "DoneStuttering" -> {"done_stuttering"}
          [] OTHER -> {"done_stuttering"}]

ViolationOf ==
    [key \in {"TypeInvariant", "BarrierCompleteness", "OutputConsistency", "PhaseOrdering"} |->
        CASE key = "TypeInvariant" -> "CarrierTypeViolation"
          [] key = "BarrierCompleteness" -> "OutputBeforeAllComplete"
          [] key = "OutputConsistency" -> "OutputSnapshotMismatch"
          [] key = "PhaseOrdering" -> "PhaseOrderViolation"
          [] OTHER -> "PhaseOrderViolation"]

OwnerOf ==
    [key \in {"StartWorker", "CompleteWorker", "Barrier", "ProduceOutput", "DoneStuttering"} |->
        CASE key = "StartWorker" -> "forkjoin-coordinator"
          [] key = "CompleteWorker" -> "worker-executor"
          [] key = "Barrier" -> "forkjoin-coordinator"
          [] key = "ProduceOutput" -> "forkjoin-coordinator"
          [] key = "DoneStuttering" -> "forkjoin-coordinator"
          [] OTHER -> "forkjoin-coordinator"]

DelegateOf ==
    [key \in {"StartWorker", "CompleteWorker", "Barrier", "ProduceOutput", "DoneStuttering"} |->
        CASE key = "StartWorker" -> {"forkjoin-coordinator"}
          [] key = "CompleteWorker" -> {"worker-executor"}
          [] key = "Barrier" -> {"forkjoin-coordinator"}
          [] key = "ProduceOutput" -> {"forkjoin-coordinator"}
          [] key = "DoneStuttering" -> {"forkjoin-coordinator"}
          [] OTHER -> {"forkjoin-coordinator"}]

AssuranceAt ==
    [key \in {"StartWorker", "CompleteWorker", "Barrier", "ProduceOutput"} |->
        CASE key = "StartWorker" -> "at-commit"
          [] key = "CompleteWorker" -> "at-commit"
          [] key = "Barrier" -> "at-commit"
          [] key = "ProduceOutput" -> "at-commit"
          [] OTHER -> "at-commit"]

WitnessPersistentObserve ==
    [key \in {"fork-ready", "fork-running", "fork-complete", "join", "done", "invalid-output"} |->
        CASE key = "fork-ready" -> TRUE
          [] key = "fork-running" -> TRUE
          [] key = "fork-complete" -> TRUE
          [] key = "join" -> TRUE
          [] key = "done" -> TRUE
          [] key = "invalid-output" -> FALSE
          [] OTHER -> FALSE]

WitnessRank ==
    [key \in {"fork-ready", "fork-running", "fork-complete", "join", "done", "invalid-output"} |->
        CASE key = "fork-ready" -> 0
          [] key = "fork-running" -> 0
          [] key = "fork-complete" -> 0
          [] key = "join" -> 0
          [] key = "done" -> 0
          [] key = "invalid-output" -> 0
          [] OTHER -> 0]

WitnessFairnessOwnerOf == [key \in {} |-> "unused"]

WitnessActionSteps ==
    [key \in {"StartWorker", "CompleteWorker", "Barrier", "ProduceOutput", "DoneStuttering"} |->
        CASE key = "StartWorker" -> {<<"fork-ready", "fork-running">>}
          [] key = "CompleteWorker" -> {<<"fork-running", "fork-complete">>}
          [] key = "Barrier" -> {<<"fork-complete", "join">>}
          [] key = "ProduceOutput" -> {<<"join", "done">>}
          [] key = "DoneStuttering" -> {<<"done", "done">>}
          [] OTHER -> {<<"done", "done">>}]

Derivation ==
    [structure |-> "ForkJoin",
     kind |-> "execution-modality",
     propertyClasses |-> {"safety"},
     stateFields |-> {"wstate", "wvalue", "phase", "output_ready", "output_snapshot"},
     observationFields |-> {"wstate", "wvalue", "phase", "output_ready", "output_snapshot"},
     implementationStateFields |-> {"wstate", "wvalue", "phase", "output_ready", "output_snapshot"},
     implementationStateMap |-> ImplementationStateMap,
     observationMap |-> ObservationMap,
     canonicalActions |-> {"StartWorker", "CompleteWorker", "Barrier", "ProduceOutput", "DoneStuttering"},
     systemActions |-> {"StartWorker", "CompleteWorker", "Barrier", "ProduceOutput", "DoneStuttering"},
     environmentActions |-> {},
     failureActions |-> {},
     commitActions |-> {"StartWorker", "CompleteWorker", "Barrier", "ProduceOutput"},
     executableActions |-> {"start_worker", "complete_worker", "barrier", "produce_output", "done_stuttering"},
     actionMap |-> ActionMap,
     obligations |-> {"TypeInvariant", "BarrierCompleteness", "OutputConsistency", "PhaseOrdering"},
     violations |-> {"CarrierTypeViolation", "OutputBeforeAllComplete", "OutputSnapshotMismatch", "PhaseOrderViolation"},
     violationOf |-> ViolationOf,
     actors |-> {"workflow-claimant", "forkjoin-coordinator", "worker-executor"},
     claimant |-> "workflow-claimant",
     ownerOf |-> OwnerOf,
     delegateOf |-> DelegateOf,
     assuranceAt |-> AssuranceAt,
     relies |-> {"finite-worker-index-set", "nonempty-worker-value-domain", "serialized-carrier-state-mutation", "atomic-completion-barrier-and-output-transitions", "complete-worker-and-coordinator-writer-inventory"},
     guarantees |-> {"forkjoin-barrier-output-safety", "atomic-barrier-license", "forkjoin-owner-ceiling", "forkjoin-written-profile-refinement"},
     runtimeProviders |-> {"forkjoin-coordinator", "worker-executor", "worker-value-provider"},
     failureCeilings |-> {"no-modeled-worker-or-coordinator-crash-retry-or-recovery", "no-modeled-torn-completion-barrier-or-output-commit", "inter-worker-communication-during-fork-is-outside-the-representation"},
     executionCarriers |-> {"ForkJoin"},
     localTheorems |-> {"ForkJoin_Proof!Safety", "ForkJoin_Proof!BarrierCompletenessSafety", "ForkJoin_Proof!OutputConsistencySafety", "ForkJoin_Proof!PhaseOrderingSafety", "ForkJoinImplRefinesSpec_Proof!RefinementThm", "TheoryKernel_Proof!ObligationPreservation", "TheoryKernel_Proof!CheckActStability", "OwnershipAssuranceKernel_Proof!OwnershipAssuranceClassification"},
     executablePointers |-> {"formal/execution/carriers/ForkJoin.tla", "formal/execution/carriers/ForkJoin_Proof.tla", "formal/execution/carriers/refinement/ForkJoin/ForkJoinImplRefinesSpec.tla", "formal/execution/carriers/refinement/ForkJoin/ForkJoinImplRefinesSpec_Proof.tla", "development-copy://automation-structures/0.3.2/src/modalities/fork_join.rs"},
     libraryPremises |-> {"canonical-fork-join-carrier", "ForkJoin-Safety", "ObligationPreservation", "CheckActStability", "OwnershipAssuranceClassification"},
     deploymentPremises |-> {"finite-worker-index-set", "nonempty-worker-value-domain", "serialized-carrier-state-mutation", "atomic-completion-barrier-and-output-transitions", "complete-worker-and-coordinator-writer-inventory"},
     residuals |-> {"no-inter-worker-noninterference-theorem", "no-eventual-worker-completion-barrier-or-output-availability", "no-scheduler-fairness-throughput-or-time-bound", "no-crash-retry-durability-or-external-effect-result"},
     evidenceCeilings |-> {"TLAPS-proves-typed-barrier-output-and-phase-safety", "inter-worker-isolation-is-a-representation-ceiling-not-a-checked-invariant", "Verus-proves-the-written-finite-index-carrier", "DoneStuttering-supplies-no-progress-credit"},
     validCases |-> {"complete-barrier-publish"},
     boundaryCases |-> {"incomplete-barrier-rejected"},
     misuseCases |-> {"worker-peer-communication"},
     failureCases |-> {"torn-output-commit"},
     globalAssumptions |-> GlobalModelingAssumptionNames,
     conformanceConditions |-> ConformanceConditions,
     applicableFamilies |-> {"obligation", "check-act", "ownership-assurance", "refinement"},
     dischargedFamilies |-> {"obligation", "check-act", "ownership-assurance", "refinement"},
     transferClasses |-> {"safety", "observation"},
     refinementStatus |-> "mechanized",
     witnessStates |-> {"fork-ready", "fork-running", "fork-complete", "join", "done", "invalid-output"},
     witnessInitial |-> {"fork-ready"},
     witnessObligationStates |-> {"fork-ready", "fork-running", "fork-complete", "join", "done"},
     witnessViolationStates |-> {"invalid-output"},
     witnessSystemSteps |-> {<<"fork-ready", "fork-running">>, <<"fork-running", "fork-complete">>, <<"fork-complete", "join">>, <<"join", "done">>, <<"done", "done">>},
     witnessEnvironmentSteps |-> {},
     witnessActionSteps |-> WitnessActionSteps,
     witnessRelySteps |-> {},
     witnessCommitSteps |-> {<<"fork-ready", "fork-running">>, <<"fork-running", "fork-complete">>, <<"fork-complete", "join">>, <<"join", "done">>},
     witnessFailureSteps |-> {},
     witnessInterferenceSteps |-> {},
     witnessCheckActMode |-> "atomic",
     witnessCheckResultStates |-> {"fork-ready", "fork-running", "fork-complete", "join", "done"},
     witnessPredicateStates |-> {"fork-ready", "fork-running", "fork-complete", "join", "done"},
     witnessActors |-> {"workflow-claimant", "forkjoin-coordinator", "worker-executor"},
     witnessProviders |-> {"forkjoin-coordinator", "worker-executor"},
     witnessClaimant |-> "workflow-claimant",
     witnessCommitOwner |-> "forkjoin-coordinator",
     witnessCommitDelegate |-> "worker-executor",
     witnessAssuranceProvider |-> "forkjoin-coordinator",
     witnessAssurancePosition |-> "at-commit",
     witnessPreventionControllers |-> {"forkjoin-coordinator", "worker-executor"},
     witnessUnavailableProviders |-> {},
     witnessPersistentObserve |-> WitnessPersistentObserve,
     witnessPersistentEvidence |-> TRUE,
     witnessRecoveryAvailable |-> FALSE,
     witnessActiveStates |-> {"fork-ready", "fork-running", "fork-complete", "join"},
     witnessClosedStates |-> {"done", "invalid-output"},
     witnessProgressSteps |-> {},
     witnessOtherSteps |-> {},
     witnessHandoffSteps |-> {<<"fork-complete", "join">>},
     witnessRankBound |-> 0,
     witnessRank |-> WitnessRank,
     witnessFairnessOwners |-> {"forkjoin-coordinator", "worker-executor"},
     witnessFairnessOwner |-> "forkjoin-coordinator",
     witnessFairnessOwnerOf |-> WitnessFairnessOwnerOf]

====
