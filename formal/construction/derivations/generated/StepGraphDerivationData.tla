---- MODULE StepGraphDerivationData ----
EXTENDS StructureDerivationSchema

\* Generated from the checked derivation record. Do not edit by hand.

ImplementationStateMap ==
    [key \in {"num_nodes", "edges", "nstate"} |->
        CASE key = "num_nodes" -> "Nodes"
          [] key = "edges" -> "Edges"
          [] key = "nstate" -> "nstate"
          [] OTHER -> "nstate"]

ObservationMap ==
    [key \in {"num_nodes", "edges", "nstate"} |->
        CASE key = "num_nodes" -> "Nodes"
          [] key = "edges" -> "Edges"
          [] key = "nstate" -> "nstate"
          [] OTHER -> "nstate"]

ActionMap ==
    [key \in {"BecomeReady", "StartRunning", "CompleteNode", "DoneStuttering"} |->
        CASE key = "BecomeReady" -> {"become_ready"}
          [] key = "StartRunning" -> {"start_running"}
          [] key = "CompleteNode" -> {"complete_node"}
          [] key = "DoneStuttering" -> {"done_stuttering"}
          [] OTHER -> {"done_stuttering"}]

ViolationOf ==
    [key \in {"TypeInvariant", "EligibilityClosed", "NoRunBeforePredecessors", "ProgressMonotonic"} |->
        CASE key = "TypeInvariant" -> "NodeStateTypeViolation"
          [] key = "EligibilityClosed" -> "EligibleBeforePredecessors"
          [] key = "NoRunBeforePredecessors" -> "RunBeforePredecessors"
          [] key = "ProgressMonotonic" -> "NodeStateRegression"
          [] OTHER -> "NodeStateRegression"]

OwnerOf ==
    [key \in {"BecomeReady", "StartRunning", "CompleteNode", "DoneStuttering"} |->
        CASE key = "BecomeReady" -> "stepgraph-executor"
          [] key = "StartRunning" -> "stepgraph-executor"
          [] key = "CompleteNode" -> "stepgraph-executor"
          [] key = "DoneStuttering" -> "stepgraph-executor"
          [] OTHER -> "stepgraph-executor"]

DelegateOf ==
    [key \in {"BecomeReady", "StartRunning", "CompleteNode", "DoneStuttering"} |->
        CASE key = "BecomeReady" -> {"stepgraph-executor"}
          [] key = "StartRunning" -> {"stepgraph-executor"}
          [] key = "CompleteNode" -> {"stepgraph-executor"}
          [] key = "DoneStuttering" -> {"stepgraph-executor"}
          [] OTHER -> {"stepgraph-executor"}]

AssuranceAt ==
    [key \in {"BecomeReady", "StartRunning", "CompleteNode"} |->
        CASE key = "BecomeReady" -> "at-commit"
          [] key = "StartRunning" -> "at-commit"
          [] key = "CompleteNode" -> "at-commit"
          [] OTHER -> "at-commit"]

WitnessPersistentObserve ==
    [key \in {"not-ready", "ready", "running", "completed", "invalid-order"} |->
        CASE key = "not-ready" -> TRUE
          [] key = "ready" -> TRUE
          [] key = "running" -> TRUE
          [] key = "completed" -> TRUE
          [] key = "invalid-order" -> FALSE
          [] OTHER -> FALSE]

WitnessRank ==
    [key \in {"not-ready", "ready", "running", "completed", "invalid-order"} |->
        CASE key = "not-ready" -> 0
          [] key = "ready" -> 0
          [] key = "running" -> 0
          [] key = "completed" -> 0
          [] key = "invalid-order" -> 0
          [] OTHER -> 0]

WitnessFairnessOwnerOf == [key \in {} |-> "unused"]

WitnessActionSteps ==
    [key \in {"BecomeReady", "StartRunning", "CompleteNode", "DoneStuttering"} |->
        CASE key = "BecomeReady" -> {<<"not-ready", "ready">>}
          [] key = "StartRunning" -> {<<"ready", "running">>}
          [] key = "CompleteNode" -> {<<"running", "completed">>}
          [] key = "DoneStuttering" -> {<<"completed", "completed">>}
          [] OTHER -> {<<"completed", "completed">>}]

Derivation ==
    [structure |-> "StepGraph",
     kind |-> "execution-modality",
     propertyClasses |-> {"safety"},
     stateFields |-> {"Nodes", "Edges", "nstate"},
     observationFields |-> {"num_nodes", "edges", "nstate"},
     implementationStateFields |-> {"num_nodes", "edges", "nstate"},
     implementationStateMap |-> ImplementationStateMap,
     observationMap |-> ObservationMap,
     canonicalActions |-> {"BecomeReady", "StartRunning", "CompleteNode", "DoneStuttering"},
     systemActions |-> {"BecomeReady", "StartRunning", "CompleteNode", "DoneStuttering"},
     environmentActions |-> {},
     failureActions |-> {},
     commitActions |-> {"BecomeReady", "StartRunning", "CompleteNode"},
     executableActions |-> {"become_ready", "start_running", "complete_node", "done_stuttering"},
     actionMap |-> ActionMap,
     obligations |-> {"TypeInvariant", "EligibilityClosed", "NoRunBeforePredecessors", "ProgressMonotonic"},
     violations |-> {"NodeStateTypeViolation", "EligibleBeforePredecessors", "RunBeforePredecessors", "NodeStateRegression"},
     violationOf |-> ViolationOf,
     actors |-> {"workflow-claimant", "stepgraph-executor"},
     claimant |-> "workflow-claimant",
     ownerOf |-> OwnerOf,
     delegateOf |-> DelegateOf,
     assuranceAt |-> AssuranceAt,
     relies |-> {"fixed-node-and-edge-topology", "executable-edge-indices-valid-and-distinct", "serialized-node-state-mutation", "atomic-predecessor-check-and-readiness-commit", "complete-node-state-writer-inventory"},
     guarantees |-> {"predecessor-eligibility-safety", "node-state-monotonic-safety", "atomic-readiness-license", "stepgraph-owner-ceiling", "stepgraph-written-profile-refinement"},
     runtimeProviders |-> {"stepgraph-executor", "fixed-topology-provider", "node-state-provider"},
     failureCeilings |-> {"no-modeled-executor-crash-retry-or-recovery", "no-modeled-topology-mutation", "cyclic-or-unschedulable-graphs-may-stall-without-violating-safety"},
     executionCarriers |-> {"StepGraph"},
     localTheorems |-> {"StepGraph_Proof!Safety", "StepGraph_Proof!NoRunBeforePredecessorsSafety", "StepGraph_Proof!ProgressMonotonicSafety", "StepGraphImplRefinesSpec_Proof!RefinementThm", "TheoryKernel_Proof!ObligationPreservation", "TheoryKernel_Proof!CheckActStability", "OwnershipAssuranceKernel_Proof!OwnershipAssuranceClassification"},
     executablePointers |-> {"formal/execution/carriers/StepGraph.tla", "formal/execution/carriers/StepGraph_Proof.tla", "formal/execution/carriers/refinement/StepGraph/StepGraphImplRefinesSpec.tla", "formal/execution/carriers/refinement/StepGraph/StepGraphImplRefinesSpec_Proof.tla", "development-copy://automation-structures/0.3.2/src/modalities/step_graph.rs"},
     libraryPremises |-> {"canonical-step-graph-carrier", "StepGraph-Safety", "NoRunBeforePredecessorsSafety", "ProgressMonotonicSafety", "ObligationPreservation", "CheckActStability", "OwnershipAssuranceClassification"},
     deploymentPremises |-> {"fixed-node-and-edge-topology", "executable-edge-indices-valid-and-distinct", "serialized-node-state-mutation", "atomic-predecessor-check-and-readiness-commit", "complete-node-state-writer-inventory"},
     residuals |-> {"no-acyclicity-or-topological-completeness-theorem", "no-eventual-readiness-running-or-completion", "no-scheduler-fairness-throughput-or-time-bound", "ProgressMonotonic-is-an-action-safety-property-not-kernel-Progress"},
     evidenceCeilings |-> {"TLAPS-proves-eligibility-and-nondecreasing-node-state-safety-for-the-written-parametric-topology", "cycles-and-self-edges-can-stall-without-falsifying-the-proof", "Verus-additionally-requires-valid-distinct-finite-edge-indices", "DoneStuttering-supplies-no-progress-credit"},
     validCases |-> {"predecessors-then-node"},
     boundaryCases |-> {"source-ready-at-init"},
     misuseCases |-> {"completion-inferred-from-monotonicity"},
     failureCases |-> {"topology-or-state-bypass"},
     globalAssumptions |-> GlobalModelingAssumptionNames,
     conformanceConditions |-> ConformanceConditions,
     applicableFamilies |-> {"obligation", "check-act", "ownership-assurance", "refinement"},
     dischargedFamilies |-> {"obligation", "check-act", "ownership-assurance", "refinement"},
     transferClasses |-> {"safety", "observation"},
     refinementStatus |-> "mechanized",
     witnessStates |-> {"not-ready", "ready", "running", "completed", "invalid-order"},
     witnessInitial |-> {"not-ready"},
     witnessObligationStates |-> {"not-ready", "ready", "running", "completed"},
     witnessViolationStates |-> {"invalid-order"},
     witnessSystemSteps |-> {<<"not-ready", "ready">>, <<"ready", "running">>, <<"running", "completed">>, <<"completed", "completed">>},
     witnessEnvironmentSteps |-> {},
     witnessActionSteps |-> WitnessActionSteps,
     witnessRelySteps |-> {},
     witnessCommitSteps |-> {<<"not-ready", "ready">>, <<"ready", "running">>, <<"running", "completed">>},
     witnessFailureSteps |-> {},
     witnessInterferenceSteps |-> {},
     witnessCheckActMode |-> "atomic",
     witnessCheckResultStates |-> {"not-ready", "ready", "running", "completed"},
     witnessPredicateStates |-> {"not-ready", "ready", "running", "completed"},
     witnessActors |-> {"workflow-claimant", "stepgraph-executor"},
     witnessProviders |-> {"stepgraph-executor"},
     witnessClaimant |-> "workflow-claimant",
     witnessCommitOwner |-> "stepgraph-executor",
     witnessCommitDelegate |-> "stepgraph-executor",
     witnessAssuranceProvider |-> "stepgraph-executor",
     witnessAssurancePosition |-> "at-commit",
     witnessPreventionControllers |-> {"stepgraph-executor"},
     witnessUnavailableProviders |-> {},
     witnessPersistentObserve |-> WitnessPersistentObserve,
     witnessPersistentEvidence |-> TRUE,
     witnessRecoveryAvailable |-> FALSE,
     witnessActiveStates |-> {"not-ready", "ready", "running"},
     witnessClosedStates |-> {"completed", "invalid-order"},
     witnessProgressSteps |-> {},
     witnessOtherSteps |-> {},
     witnessHandoffSteps |-> {<<"not-ready", "ready">>},
     witnessRankBound |-> 0,
     witnessRank |-> WitnessRank,
     witnessFairnessOwners |-> {"stepgraph-executor"},
     witnessFairnessOwner |-> "stepgraph-executor",
     witnessFairnessOwnerOf |-> WitnessFairnessOwnerOf]

====
