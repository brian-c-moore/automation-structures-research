---- MODULE StreamGraphDerivationData ----
EXTENDS StructureDerivationSchema

\* Generated from the checked derivation record. Do not edit by hand.

ImplementationStateMap ==
    [key \in {"q1", "q2", "q3", "ingested", "emitted"} |->
        CASE key = "q1" -> "q1"
          [] key = "q2" -> "q2"
          [] key = "q3" -> "q3"
          [] key = "ingested" -> "ingested"
          [] key = "emitted" -> "emitted"
          [] OTHER -> "emitted"]

ObservationMap ==
    [key \in {"q1", "q2", "q3", "ingested", "emitted"} |->
        CASE key = "q1" -> "q1"
          [] key = "q2" -> "q2"
          [] key = "q3" -> "q3"
          [] key = "ingested" -> "ingested"
          [] key = "emitted" -> "emitted"
          [] OTHER -> "emitted"]

ActionMap ==
    [key \in {"SourceIngest", "Middle2Fire", "Middle3Fire", "SinkConsume3", "SinkConsume4", "DoneStuttering"} |->
        CASE key = "SourceIngest" -> {"source_ingest"}
          [] key = "Middle2Fire" -> {"middle2_fire"}
          [] key = "Middle3Fire" -> {"middle3_fire"}
          [] key = "SinkConsume3" -> {"sink_consume"}
          [] key = "SinkConsume4" -> {"sink_consume"}
          [] key = "DoneStuttering" -> {"done_stuttering"}
          [] OTHER -> {"done_stuttering"}]

ViolationOf ==
    [key \in {"TypeInvariant", "BackpressureCorrect", "OccupancyCountConservation", "SomeActionEnabled"} |->
        CASE key = "TypeInvariant" -> "QueueTypeViolation"
          [] key = "BackpressureCorrect" -> "CapacityExceeded"
          [] key = "OccupancyCountConservation" -> "OccupancyConservationViolation"
          [] key = "SomeActionEnabled" -> "NoEnabledCarrierAction"
          [] OTHER -> "NoEnabledCarrierAction"]

OwnerOf ==
    [key \in {"SourceIngest", "Middle2Fire", "Middle3Fire", "SinkConsume3", "SinkConsume4", "DoneStuttering"} |->
        CASE key = "SourceIngest" -> "streamgraph-executor"
          [] key = "Middle2Fire" -> "streamgraph-executor"
          [] key = "Middle3Fire" -> "streamgraph-executor"
          [] key = "SinkConsume3" -> "streamgraph-executor"
          [] key = "SinkConsume4" -> "streamgraph-executor"
          [] key = "DoneStuttering" -> "streamgraph-executor"
          [] OTHER -> "streamgraph-executor"]

DelegateOf ==
    [key \in {"SourceIngest", "Middle2Fire", "Middle3Fire", "SinkConsume3", "SinkConsume4", "DoneStuttering"} |->
        CASE key = "SourceIngest" -> {"streamgraph-executor"}
          [] key = "Middle2Fire" -> {"streamgraph-executor"}
          [] key = "Middle3Fire" -> {"streamgraph-executor"}
          [] key = "SinkConsume3" -> {"streamgraph-executor"}
          [] key = "SinkConsume4" -> {"streamgraph-executor"}
          [] key = "DoneStuttering" -> {"streamgraph-executor"}
          [] OTHER -> {"streamgraph-executor"}]

AssuranceAt ==
    [key \in {"SourceIngest", "Middle2Fire", "Middle3Fire", "SinkConsume3", "SinkConsume4"} |->
        CASE key = "SourceIngest" -> "at-commit"
          [] key = "Middle2Fire" -> "at-commit"
          [] key = "Middle3Fire" -> "at-commit"
          [] key = "SinkConsume3" -> "at-commit"
          [] key = "SinkConsume4" -> "at-commit"
          [] OTHER -> "at-commit"]

WitnessPersistentObserve ==
    [key \in {"open", "buffered", "drained", "invalid-stream"} |->
        CASE key = "open" -> TRUE
          [] key = "buffered" -> TRUE
          [] key = "drained" -> TRUE
          [] key = "invalid-stream" -> FALSE
          [] OTHER -> FALSE]

WitnessRank ==
    [key \in {"open", "buffered", "drained", "invalid-stream"} |->
        CASE key = "open" -> 0
          [] key = "buffered" -> 0
          [] key = "drained" -> 0
          [] key = "invalid-stream" -> 0
          [] OTHER -> 0]

WitnessFairnessOwnerOf == [key \in {} |-> "unused"]

WitnessActionSteps ==
    [key \in {"SourceIngest", "Middle2Fire", "Middle3Fire", "SinkConsume3", "SinkConsume4", "DoneStuttering"} |->
        CASE key = "SourceIngest" -> {<<"open", "buffered">>}
          [] key = "Middle2Fire" -> {<<"buffered", "buffered">>}
          [] key = "Middle3Fire" -> {<<"buffered", "buffered">>}
          [] key = "SinkConsume3" -> {<<"buffered", "drained">>}
          [] key = "SinkConsume4" -> {<<"buffered", "drained">>}
          [] key = "DoneStuttering" -> {<<"drained", "drained">>}
          [] OTHER -> {<<"drained", "drained">>}]

Derivation ==
    [structure |-> "StreamGraph",
     kind |-> "execution-modality",
     propertyClasses |-> {"safety"},
     stateFields |-> {"q1", "q2", "q3", "ingested", "emitted"},
     observationFields |-> {"q1", "q2", "q3", "ingested", "emitted"},
     implementationStateFields |-> {"q1", "q2", "q3", "ingested", "emitted"},
     implementationStateMap |-> ImplementationStateMap,
     observationMap |-> ObservationMap,
     canonicalActions |-> {"SourceIngest", "Middle2Fire", "Middle3Fire", "SinkConsume3", "SinkConsume4", "DoneStuttering"},
     systemActions |-> {"SourceIngest", "Middle2Fire", "Middle3Fire", "SinkConsume3", "SinkConsume4", "DoneStuttering"},
     environmentActions |-> {},
     failureActions |-> {},
     commitActions |-> {"SourceIngest", "Middle2Fire", "Middle3Fire", "SinkConsume3", "SinkConsume4"},
     executableActions |-> {"source_ingest", "middle2_fire", "middle3_fire", "sink_consume", "done_stuttering"},
     actionMap |-> ActionMap,
     obligations |-> {"TypeInvariant", "BackpressureCorrect", "OccupancyCountConservation", "SomeActionEnabled"},
     violations |-> {"QueueTypeViolation", "CapacityExceeded", "OccupancyConservationViolation", "NoEnabledCarrierAction"},
     violationOf |-> ViolationOf,
     actors |-> {"workflow-claimant", "streamgraph-executor"},
     claimant |-> "workflow-claimant",
     ownerOf |-> OwnerOf,
     delegateOf |-> DelegateOf,
     assuranceAt |-> AssuranceAt,
     relies |-> {"specified-chain-length-three-or-four", "positive-finite-queue-capacity", "bounded-input-count-and-nonempty-record-domain", "serialized-atomic-queue-and-counter-mutation", "complete-stream-state-writer-inventory"},
     guarantees |-> {"linear-stream-conservation-safety", "state-level-enabledness", "atomic-backpressure-license", "streamgraph-owner-ceiling", "streamgraph-written-profile-refinement"},
     runtimeProviders |-> {"streamgraph-executor", "record-provider", "queue-capacity-provider"},
     failureCeilings |-> {"no-modeled-operator-crash-retry-or-recovery", "no-modeled-torn-queue-counter-commit", "fanout-merge-and-arbitrary-graph-topologies-outside-specified-carrier"},
     executionCarriers |-> {"StreamGraph"},
     localTheorems |-> {"StreamGraph_Proof!Safety", "StreamGraph_Proof!BackpressureSafety", "StreamGraph_Proof!OccupancyCountConservationSafety", "StreamGraph_Proof!SomeActionEnabledSafety", "StreamGraphImplRefinesSpec_Proof!RefinementThm", "TheoryKernel_Proof!ObligationPreservation", "TheoryKernel_Proof!CheckActStability", "OwnershipAssuranceKernel_Proof!OwnershipAssuranceClassification"},
     executablePointers |-> {"formal/execution/carriers/StreamGraph.tla", "formal/execution/carriers/StreamGraph_Proof.tla", "formal/execution/carriers/refinement/StreamGraph/StreamGraphImplRefinesSpec.tla", "formal/execution/carriers/refinement/StreamGraph/StreamGraphImplRefinesSpec_Proof.tla", "crate://automation-structures/0.2.3/src/modalities/stream_graph.rs"},
     libraryPremises |-> {"canonical-linear-stream-carrier", "StreamGraph-Safety", "SomeActionEnabledSafety", "ObligationPreservation", "CheckActStability", "OwnershipAssuranceClassification"},
     deploymentPremises |-> {"specified-chain-length-three-or-four", "positive-finite-queue-capacity", "bounded-input-count-and-nonempty-record-domain", "serialized-atomic-queue-and-counter-mutation", "complete-stream-state-writer-inventory"},
     residuals |-> {"no-fanout-merge-or-arbitrary-graph-conservation", "OccupancyCountConservation-is-not-durability-or-exactly-once-delivery", "state-level-enabledness-does-not-imply-eventual-consumption-or-drain", "no-scheduler-fairness-throughput-latency-or-time-bound"},
     evidenceCeilings |-> {"TLAPS-proves-capacity-occupancy-and-enabled-action-safety-for-exact-three-four-node-chains", "the-supplemental-StreamGraphFanout-progress-profile-is-not-this-carrier", "Verus-proves-the-written-finite-u64-chain-carrier", "DoneStuttering-supplies-no-progress-credit"},
     validCases |-> {"ingest-transfer-consume"},
     boundaryCases |-> {"full-queue-backpressure"},
     misuseCases |-> {"fanout-read-into-chain"},
     failureCases |-> {"torn-queue-counter-update"},
     globalAssumptions |-> GlobalModelingAssumptionNames,
     conformanceConditions |-> ConformanceConditions,
     applicableFamilies |-> {"obligation", "check-act", "ownership-assurance", "refinement"},
     dischargedFamilies |-> {"obligation", "check-act", "ownership-assurance", "refinement"},
     transferClasses |-> {"safety", "observation"},
     refinementStatus |-> "mechanized",
     witnessStates |-> {"open", "buffered", "drained", "invalid-stream"},
     witnessInitial |-> {"open"},
     witnessObligationStates |-> {"open", "buffered", "drained"},
     witnessViolationStates |-> {"invalid-stream"},
     witnessSystemSteps |-> {<<"open", "buffered">>, <<"buffered", "buffered">>, <<"buffered", "drained">>, <<"drained", "drained">>},
     witnessEnvironmentSteps |-> {},
     witnessActionSteps |-> WitnessActionSteps,
     witnessRelySteps |-> {},
     witnessCommitSteps |-> {<<"open", "buffered">>, <<"buffered", "buffered">>, <<"buffered", "drained">>},
     witnessFailureSteps |-> {},
     witnessInterferenceSteps |-> {},
     witnessCheckActMode |-> "atomic",
     witnessCheckResultStates |-> {"open", "buffered", "drained"},
     witnessPredicateStates |-> {"open", "buffered", "drained"},
     witnessActors |-> {"workflow-claimant", "streamgraph-executor"},
     witnessProviders |-> {"streamgraph-executor"},
     witnessClaimant |-> "workflow-claimant",
     witnessCommitOwner |-> "streamgraph-executor",
     witnessCommitDelegate |-> "streamgraph-executor",
     witnessAssuranceProvider |-> "streamgraph-executor",
     witnessAssurancePosition |-> "at-commit",
     witnessPreventionControllers |-> {"streamgraph-executor"},
     witnessUnavailableProviders |-> {},
     witnessPersistentObserve |-> WitnessPersistentObserve,
     witnessPersistentEvidence |-> TRUE,
     witnessRecoveryAvailable |-> FALSE,
     witnessActiveStates |-> {"open", "buffered"},
     witnessClosedStates |-> {"drained", "invalid-stream"},
     witnessProgressSteps |-> {},
     witnessOtherSteps |-> {},
     witnessHandoffSteps |-> {<<"buffered", "buffered">>},
     witnessRankBound |-> 0,
     witnessRank |-> WitnessRank,
     witnessFairnessOwners |-> {"streamgraph-executor"},
     witnessFairnessOwner |-> "streamgraph-executor",
     witnessFairnessOwnerOf |-> WitnessFairnessOwnerOf]

====
