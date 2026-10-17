---- MODULE RelationshipGraphDerivationData ----
EXTENDS StructureDerivationSchema

\* Generated from the checked derivation record. Do not edit by hand.

ImplementationStateMap ==
    [key \in {"edges", "adjacency"} |->
        CASE key = "edges" -> "edges"
          [] key = "adjacency" -> "adjacency"
          [] OTHER -> "adjacency"]

ObservationMap ==
    [key \in {"edges", "adjacency"} |->
        CASE key = "edges" -> "edges"
          [] key = "adjacency" -> "adjacency"
          [] OTHER -> "adjacency"]

ActionMap ==
    [key \in {"AddEdge", "RemoveEdge"} |->
        CASE key = "AddEdge" -> {"add_edge"}
          [] key = "RemoveEdge" -> {"remove_edge"}
          [] OTHER -> {"remove_edge"}]

ViolationOf ==
    [key \in {"AdjacencyConsistency", "NoSelfLoops"} |->
        CASE key = "AdjacencyConsistency" -> "AdjacencyProjectionMismatch"
          [] key = "NoSelfLoops" -> "SelfLoopPresent"
          [] OTHER -> "SelfLoopPresent"]

OwnerOf ==
    [key \in {"AddEdge", "RemoveEdge"} |->
        CASE key = "AddEdge" -> "graph-authority"
          [] key = "RemoveEdge" -> "graph-authority"
          [] OTHER -> "graph-authority"]

DelegateOf ==
    [key \in {"AddEdge", "RemoveEdge"} |->
        CASE key = "AddEdge" -> {"graph-authority"}
          [] key = "RemoveEdge" -> {"graph-authority"}
          [] OTHER -> {"graph-authority"}]

AssuranceAt ==
    [key \in {"AddEdge", "RemoveEdge"} |->
        CASE key = "AddEdge" -> "at-commit"
          [] key = "RemoveEdge" -> "at-commit"
          [] OTHER -> "at-commit"]

WitnessPersistentObserve ==
    [key \in {"empty-graph", "linked-graph", "inconsistent-graph"} |->
        CASE key = "empty-graph" -> TRUE
          [] key = "linked-graph" -> TRUE
          [] key = "inconsistent-graph" -> FALSE
          [] OTHER -> FALSE]

WitnessRank ==
    [key \in {"empty-graph", "linked-graph", "inconsistent-graph"} |->
        CASE key = "empty-graph" -> 0
          [] key = "linked-graph" -> 0
          [] key = "inconsistent-graph" -> 0
          [] OTHER -> 0]

WitnessFairnessOwnerOf == [key \in {} |-> "unused"]

WitnessActionSteps ==
    [key \in {"AddEdge", "RemoveEdge"} |->
        CASE key = "AddEdge" -> {<<"empty-graph", "linked-graph">>}
          [] key = "RemoveEdge" -> {<<"linked-graph", "empty-graph">>}
          [] OTHER -> {<<"linked-graph", "empty-graph">>}]

Derivation ==
    [structure |-> "RelationshipGraph",
     kind |-> "named-composition",
     propertyClasses |-> {"safety"},
     stateFields |-> {"edges", "adjacency"},
     observationFields |-> {"edges", "adjacency"},
     implementationStateFields |-> {"edges", "adjacency"},
     implementationStateMap |-> ImplementationStateMap,
     observationMap |-> ObservationMap,
     canonicalActions |-> {"AddEdge", "RemoveEdge"},
     systemActions |-> {"AddEdge", "RemoveEdge"},
     environmentActions |-> {},
     failureActions |-> {},
     commitActions |-> {"AddEdge", "RemoveEdge"},
     executableActions |-> {"add_edge", "remove_edge"},
     actionMap |-> ActionMap,
     obligations |-> {"AdjacencyConsistency", "NoSelfLoops"},
     violations |-> {"AdjacencyProjectionMismatch", "SelfLoopPresent"},
     violationOf |-> ViolationOf,
     actors |-> {"graph-claimant", "graph-authority"},
     claimant |-> "graph-claimant",
     ownerOf |-> OwnerOf,
     delegateOf |-> DelegateOf,
     assuranceAt |-> AssuranceAt,
     relies |-> {"finite-indexed-node-universe", "serialized-edge-adjacency-mutation", "atomic-dual-view-commit"},
     guarantees |-> {"relationshipgraph-written-profile-refinement", "graph-projection-consistency", "graph-guarded-update", "graph-owner-ceiling"},
     runtimeProviders |-> {"graph-authority", "exclusive-mutation-provider", "finite-index-provider"},
     failureCeilings |-> {"no-modeled-crash-or-torn-dual-view", "concurrent-bypass-writer-outside-boundary", "finite-indexed-directed-graph-only"},
     executionCarriers |-> {"Sequential"},
     localTheorems |-> {"RelationshipGraphImplRefinesSpec_Proof!RefinementThm", "RelationshipGraph_Proof!Safety", "RelationshipGraph_Proof!AdjacencyConsistencySafety", "RelationshipGraph_Proof!NoSelfLoopsSafety", "TheoryKernel_Proof!ObligationPreservation", "TheoryKernel_Proof!CheckActStability", "OwnershipAssuranceKernel_Proof!OwnershipAssuranceClassification"},
     executablePointers |-> {"formal/structures/RelationshipGraph/refinement/RelationshipGraphImplRefinesSpec.tla", "formal/structures/RelationshipGraph/refinement/RelationshipGraphImplRefinesSpec_Proof.tla", "development-copy://automation-structures/0.3.2/src/compositions/relationship_graph.rs", "formal/structures/RelationshipGraph/RelationshipGraph.tla", "formal/structures/RelationshipGraph/RelationshipGraph_Proof.tla"},
     libraryPremises |-> {"RelationshipGraph-written-contract-refinement-profile", "canonical-directed-graph-machine", "RelationshipGraph-Safety", "ObligationPreservation", "CheckActStability", "OwnershipAssuranceClassification"},
     deploymentPremises |-> {"NodesFinite", "WeightsTyped", "serialized-edge-adjacency-mutation", "atomic-dual-view-commit", "complete-graph-writer-inventory"},
     residuals |-> {"formal-correspondence-is-limited-to-the-written-state-action-and-premise-map", "no-reciprocal-edge-claim", "no-path-reachability-or-acyclicity-result", "no-durable-or-concurrent-graph-protocol"},
     evidenceCeilings |-> {"implementation-refinement-covers-only-the-written-bounded-contract-profile", "TLAPS-proves-directed-edge-projection", "Verus-proves-the-duplicate-free-vector-representation", "no-claim-that-adjacency-is-symmetric"},
     validCases |-> {"add-and-remove-edge"},
     boundaryCases |-> {"duplicate-add"},
     misuseCases |-> {"self-loop"},
     failureCases |-> {"torn-dual-view"},
     globalAssumptions |-> GlobalModelingAssumptionNames,
     conformanceConditions |-> ConformanceConditions,
     applicableFamilies |-> {"obligation", "check-act", "ownership-assurance", "refinement"},
     dischargedFamilies |-> {"obligation", "check-act", "ownership-assurance", "refinement"},
     transferClasses |-> {"safety"},
     refinementStatus |-> "mechanized",
     witnessStates |-> {"empty-graph", "linked-graph", "inconsistent-graph"},
     witnessInitial |-> {"empty-graph"},
     witnessObligationStates |-> {"empty-graph", "linked-graph"},
     witnessViolationStates |-> {"inconsistent-graph"},
     witnessSystemSteps |-> {<<"empty-graph", "linked-graph">>, <<"linked-graph", "empty-graph">>},
     witnessEnvironmentSteps |-> {},
     witnessActionSteps |-> WitnessActionSteps,
     witnessRelySteps |-> {},
     witnessCommitSteps |-> {<<"empty-graph", "linked-graph">>, <<"linked-graph", "empty-graph">>},
     witnessFailureSteps |-> {},
     witnessInterferenceSteps |-> {},
     witnessCheckActMode |-> "atomic",
     witnessCheckResultStates |-> {"empty-graph", "linked-graph"},
     witnessPredicateStates |-> {"empty-graph", "linked-graph"},
     witnessActors |-> {"graph-claimant", "graph-authority"},
     witnessProviders |-> {"graph-authority"},
     witnessClaimant |-> "graph-claimant",
     witnessCommitOwner |-> "graph-authority",
     witnessCommitDelegate |-> "graph-authority",
     witnessAssuranceProvider |-> "graph-authority",
     witnessAssurancePosition |-> "at-commit",
     witnessPreventionControllers |-> {"graph-authority"},
     witnessUnavailableProviders |-> {},
     witnessPersistentObserve |-> WitnessPersistentObserve,
     witnessPersistentEvidence |-> TRUE,
     witnessRecoveryAvailable |-> FALSE,
     witnessActiveStates |-> {"empty-graph", "linked-graph"},
     witnessClosedStates |-> {},
     witnessProgressSteps |-> {},
     witnessOtherSteps |-> {},
     witnessHandoffSteps |-> {},
     witnessRankBound |-> 0,
     witnessRank |-> WitnessRank,
     witnessFairnessOwners |-> {"graph-authority"},
     witnessFairnessOwner |-> "graph-authority",
     witnessFairnessOwnerOf |-> WitnessFairnessOwnerOf]

====
