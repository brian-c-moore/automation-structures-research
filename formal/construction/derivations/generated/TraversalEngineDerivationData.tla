---- MODULE TraversalEngineDerivationData ----
EXTENDS StructureDerivationSchema

\* Generated from the checked derivation record. Do not edit by hand.

ImplementationStateMap ==
    [key \in {"budget_remaining", "visited", "accepted", "queue"} |->
        CASE key = "budget_remaining" -> "budget_remaining"
          [] key = "visited" -> "visited"
          [] key = "accepted" -> "accepted"
          [] key = "queue" -> "queue"
          [] OTHER -> "queue"]

ObservationMap ==
    [key \in {"budget_remaining", "visited", "accepted", "queue"} |->
        CASE key = "budget_remaining" -> "budget_remaining"
          [] key = "visited" -> "visited"
          [] key = "accepted" -> "accepted"
          [] key = "queue" -> "queue"
          [] OTHER -> "queue"]

ActionMap ==
    [key \in {"VisitNode", "Skip", "Terminate"} |->
        CASE key = "VisitNode" -> {"visit_node"}
          [] key = "Skip" -> {"skip"}
          [] key = "Terminate" -> {"terminate"}
          [] OTHER -> {"terminate"}]

ViolationOf ==
    [key \in {"AcceptedCostAccounting", "AcceptedSubsetVisited"} |->
        CASE key = "AcceptedCostAccounting" -> "AcceptedCostMismatch"
          [] key = "AcceptedSubsetVisited" -> "AcceptedWithoutVisit"
          [] OTHER -> "AcceptedWithoutVisit"]

OwnerOf ==
    [key \in {"VisitNode", "Skip", "Terminate"} |->
        CASE key = "VisitNode" -> "traversal-authority"
          [] key = "Skip" -> "traversal-authority"
          [] key = "Terminate" -> "traversal-authority"
          [] OTHER -> "traversal-authority"]

DelegateOf ==
    [key \in {"VisitNode", "Skip", "Terminate"} |->
        CASE key = "VisitNode" -> {"traversal-authority"}
          [] key = "Skip" -> {"traversal-authority"}
          [] key = "Terminate" -> {"traversal-authority"}
          [] OTHER -> {"traversal-authority"}]

AssuranceAt ==
    [key \in {"VisitNode", "Skip"} |->
        CASE key = "VisitNode" -> "at-commit"
          [] key = "Skip" -> "at-commit"
          [] OTHER -> "at-commit"]

WitnessPersistentObserve ==
    [key \in {"queued", "processed", "invalid-traversal"} |->
        CASE key = "queued" -> TRUE
          [] key = "processed" -> TRUE
          [] key = "invalid-traversal" -> FALSE
          [] OTHER -> FALSE]

WitnessRank ==
    [key \in {"queued", "processed", "invalid-traversal"} |->
        CASE key = "queued" -> 0
          [] key = "processed" -> 0
          [] key = "invalid-traversal" -> 0
          [] OTHER -> 0]

WitnessFairnessOwnerOf == [key \in {} |-> "unused"]

WitnessActionSteps ==
    [key \in {"VisitNode", "Skip", "Terminate"} |->
        CASE key = "VisitNode" -> {<<"queued", "processed">>}
          [] key = "Skip" -> {<<"queued", "processed">>}
          [] key = "Terminate" -> {<<"processed", "processed">>}
          [] OTHER -> {<<"processed", "processed">>}]

Derivation ==
    [structure |-> "TraversalEngine",
     kind |-> "named-composition",
     propertyClasses |-> {"safety"},
     stateFields |-> {"budget_remaining", "visited", "accepted", "queue"},
     observationFields |-> {"budget_remaining", "visited", "accepted", "queue"},
     implementationStateFields |-> {"budget_remaining", "visited", "accepted", "queue"},
     implementationStateMap |-> ImplementationStateMap,
     observationMap |-> ObservationMap,
     canonicalActions |-> {"VisitNode", "Skip", "Terminate"},
     systemActions |-> {"VisitNode", "Skip", "Terminate"},
     environmentActions |-> {},
     failureActions |-> {},
     commitActions |-> {"VisitNode", "Skip"},
     executableActions |-> {"visit_node", "skip", "terminate"},
     actionMap |-> ActionMap,
     obligations |-> {"AcceptedCostAccounting", "AcceptedSubsetVisited"},
     violations |-> {"AcceptedCostMismatch", "AcceptedWithoutVisit"},
     violationOf |-> ViolationOf,
     actors |-> {"traversal-claimant", "traversal-authority"},
     claimant |-> "traversal-claimant",
     ownerOf |-> OwnerOf,
     delegateOf |-> DelegateOf,
     assuranceAt |-> AssuranceAt,
     relies |-> {"finite-node-universe-with-root", "serialized-budget-visited-accepted-queue-mutation", "atomic-visit-admission-and-budget-deduction"},
     guarantees |-> {"traversalengine-written-profile-refinement", "traversal-budget-visit-safety", "atomic-visit-license", "traversal-owner-ceiling"},
     runtimeProviders |-> {"traversal-authority", "finite-graph-provider", "exclusive-mutation-provider"},
     failureCeilings |-> {"no-modeled-crash-or-torn-visit-commit", "concurrent-bypass-writer-outside-boundary", "fixed-cost-root-star-instance"},
     executionCarriers |-> {"Sequential"},
     localTheorems |-> {"TraversalEngineImplRefinesSpec_Proof!RefinementThm", "TraversalEngine_Proof!Safety", "TraversalEngine_Proof!AcceptedCostAccountingSafety", "TraversalEngine_Proof!AcceptedSubsetVisitedSafety", "TheoryKernel_Proof!ObligationPreservation", "TheoryKernel_Proof!CheckActStability", "OwnershipAssuranceKernel_Proof!OwnershipAssuranceClassification"},
     executablePointers |-> {"formal/structures/TraversalEngine/refinement/TraversalEngineImplRefinesSpec.tla", "formal/structures/TraversalEngine/refinement/TraversalEngineImplRefinesSpec_Proof.tla", "crate://automation-structures/0.2.3/src/compositions/traversal_engine.rs", "formal/structures/TraversalEngine/TraversalEngine.tla", "formal/structures/TraversalEngine/TraversalEngine_Proof.tla"},
     libraryPremises |-> {"TraversalEngine-written-contract-refinement-profile", "canonical-root-star-traversal-machine", "TraversalEngine-Safety", "ObligationPreservation", "CheckActStability", "OwnershipAssuranceClassification"},
     deploymentPremises |-> {"MaxBudgetType", "RootInNodes", "finite-node-universe-with-root", "serialized-budget-visited-accepted-queue-mutation", "atomic-visit-admission-and-budget-deduction"},
     residuals |-> {"formal-correspondence-is-limited-to-the-written-state-action-and-premise-map", "no-eventual-queue-drain-or-traversal-completeness", "no-general-graph-topology-result", "no-variable-cost-accounting-result"},
     evidenceCeilings |-> {"implementation-refinement-covers-only-the-written-bounded-contract-profile", "TLAPS-proves-exact-fixed-cost-accounting-and-accepted-subset-visited", "Verus-proves-the-written-u64-root-star-carrier", "Terminate-is-stuttering-and-supplies-no-progress-credit"},
     validCases |-> {"visit-affordable-node"},
     boundaryCases |-> {"unaffordable-visit"},
     misuseCases |-> {"accept-without-visit"},
     failureCases |-> {"torn-visit-budget-commit"},
     globalAssumptions |-> GlobalModelingAssumptionNames,
     conformanceConditions |-> ConformanceConditions,
     applicableFamilies |-> {"obligation", "check-act", "ownership-assurance", "refinement"},
     dischargedFamilies |-> {"obligation", "check-act", "ownership-assurance", "refinement"},
     transferClasses |-> {"safety"},
     refinementStatus |-> "mechanized",
     witnessStates |-> {"queued", "processed", "invalid-traversal"},
     witnessInitial |-> {"queued"},
     witnessObligationStates |-> {"queued", "processed"},
     witnessViolationStates |-> {"invalid-traversal"},
     witnessSystemSteps |-> {<<"queued", "processed">>, <<"processed", "processed">>},
     witnessEnvironmentSteps |-> {},
     witnessActionSteps |-> WitnessActionSteps,
     witnessRelySteps |-> {},
     witnessCommitSteps |-> {<<"queued", "processed">>},
     witnessFailureSteps |-> {},
     witnessInterferenceSteps |-> {},
     witnessCheckActMode |-> "atomic",
     witnessCheckResultStates |-> {"queued", "processed"},
     witnessPredicateStates |-> {"queued", "processed"},
     witnessActors |-> {"traversal-claimant", "traversal-authority"},
     witnessProviders |-> {"traversal-authority"},
     witnessClaimant |-> "traversal-claimant",
     witnessCommitOwner |-> "traversal-authority",
     witnessCommitDelegate |-> "traversal-authority",
     witnessAssuranceProvider |-> "traversal-authority",
     witnessAssurancePosition |-> "at-commit",
     witnessPreventionControllers |-> {"traversal-authority"},
     witnessUnavailableProviders |-> {},
     witnessPersistentObserve |-> WitnessPersistentObserve,
     witnessPersistentEvidence |-> TRUE,
     witnessRecoveryAvailable |-> FALSE,
     witnessActiveStates |-> {"queued", "processed"},
     witnessClosedStates |-> {},
     witnessProgressSteps |-> {},
     witnessOtherSteps |-> {},
     witnessHandoffSteps |-> {},
     witnessRankBound |-> 0,
     witnessRank |-> WitnessRank,
     witnessFairnessOwners |-> {"traversal-authority"},
     witnessFairnessOwner |-> "traversal-authority",
     witnessFairnessOwnerOf |-> WitnessFairnessOwnerOf]

====
