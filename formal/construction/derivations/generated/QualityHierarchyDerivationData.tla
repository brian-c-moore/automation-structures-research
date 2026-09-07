---- MODULE QualityHierarchyDerivationData ----
EXTENDS StructureDerivationSchema

\* Generated from the checked derivation record. Do not edit by hand.

ImplementationStateMap ==
    [key \in {"level", "cost", "children", "parent"} |->
        CASE key = "level" -> "level"
          [] key = "cost" -> "cost"
          [] key = "children" -> "children"
          [] key = "parent" -> "parent"
          [] OTHER -> "parent"]

ObservationMap ==
    [key \in {"level", "cost", "children", "parent"} |->
        CASE key = "level" -> "level"
          [] key = "cost" -> "cost"
          [] key = "children" -> "children"
          [] key = "parent" -> "parent"
          [] OTHER -> "parent"]

ActionMap ==
    [key \in {"AddChild", "SetNodeProperties"} |->
        CASE key = "AddChild" -> {"add_child"}
          [] key = "SetNodeProperties" -> {"set_node_properties"}
          [] OTHER -> {"set_node_properties"}]

ViolationOf ==
    [key \in {"StrictLevelDescent", "ParentEdgeAgreement", "CostMonotonicity"} |->
        CASE key = "StrictLevelDescent" -> "NonDescendingLevelEdge"
          [] key = "ParentEdgeAgreement" -> "ParentProjectionMismatch"
          [] key = "CostMonotonicity" -> "CostOrderViolation"
          [] OTHER -> "CostOrderViolation"]

OwnerOf ==
    [key \in {"AddChild", "SetNodeProperties"} |->
        CASE key = "AddChild" -> "hierarchy-authority"
          [] key = "SetNodeProperties" -> "hierarchy-authority"
          [] OTHER -> "hierarchy-authority"]

DelegateOf ==
    [key \in {"AddChild", "SetNodeProperties"} |->
        CASE key = "AddChild" -> {"hierarchy-authority"}
          [] key = "SetNodeProperties" -> {"hierarchy-authority"}
          [] OTHER -> {"hierarchy-authority"}]

AssuranceAt ==
    [key \in {"AddChild", "SetNodeProperties"} |->
        CASE key = "AddChild" -> "at-commit"
          [] key = "SetNodeProperties" -> "at-commit"
          [] OTHER -> "at-commit"]

WitnessPersistentObserve ==
    [key \in {"isolated", "linked", "invalid-edge"} |->
        CASE key = "isolated" -> TRUE
          [] key = "linked" -> TRUE
          [] key = "invalid-edge" -> FALSE
          [] OTHER -> FALSE]

WitnessRank ==
    [key \in {"isolated", "linked", "invalid-edge"} |->
        CASE key = "isolated" -> 0
          [] key = "linked" -> 0
          [] key = "invalid-edge" -> 0
          [] OTHER -> 0]

WitnessFairnessOwnerOf == [key \in {} |-> "unused"]

WitnessActionSteps ==
    [key \in {"AddChild", "SetNodeProperties"} |->
        CASE key = "AddChild" -> {<<"isolated", "linked">>}
          [] key = "SetNodeProperties" -> {<<"isolated", "isolated">>}
          [] OTHER -> {<<"isolated", "isolated">>}]

Derivation ==
    [structure |-> "QualityHierarchy",
     kind |-> "abstraction-primitive",
     propertyClasses |-> {"safety"},
     stateFields |-> {"level", "cost", "children", "parent"},
     observationFields |-> {"level", "cost", "children", "parent"},
     implementationStateFields |-> {"level", "cost", "children", "parent"},
     implementationStateMap |-> ImplementationStateMap,
     observationMap |-> ObservationMap,
     canonicalActions |-> {"AddChild", "SetNodeProperties"},
     systemActions |-> {"AddChild", "SetNodeProperties"},
     environmentActions |-> {},
     failureActions |-> {},
     commitActions |-> {"AddChild", "SetNodeProperties"},
     executableActions |-> {"add_child", "set_node_properties"},
     actionMap |-> ActionMap,
     obligations |-> {"StrictLevelDescent", "ParentEdgeAgreement", "CostMonotonicity"},
     violations |-> {"NonDescendingLevelEdge", "ParentProjectionMismatch", "CostOrderViolation"},
     violationOf |-> ViolationOf,
     actors |-> {"hierarchy-claimant", "hierarchy-authority"},
     claimant |-> "hierarchy-claimant",
     ownerOf |-> OwnerOf,
     delegateOf |-> DelegateOf,
     assuranceAt |-> AssuranceAt,
     relies |-> {"finite-node-universe", "serialized-hierarchy-mutation", "atomic-edge-parent-commit"},
     guarantees |-> {"qualityhierarchy-written-profile-refinement", "hierarchy-edge-safety", "hierarchy-guarded-update", "hierarchy-owner-ceiling"},
     runtimeProviders |-> {"hierarchy-authority", "finite-index-provider", "exclusive-mutation-provider"},
     failureCeilings |-> {"no-modeled-crash-or-torn-edge-parent-write", "concurrent-bypass-writer-outside-boundary", "finite-single-parent-hierarchy-only"},
     executionCarriers |-> {"Sequential"},
     localTheorems |-> {"QualityHierarchyImplRefinesSpec_Proof!RefinementThm", "QualityHierarchy_Proof!Safety", "QualityHierarchy_Proof!StrictLevelDescentSafety", "QualityHierarchy_Proof!ParentEdgeAgreementSafety", "QualityHierarchy_Proof!CostMonotonicitySafety", "TheoryKernel_Proof!ObligationPreservation", "TheoryKernel_Proof!CheckActStability", "OwnershipAssuranceKernel_Proof!OwnershipAssuranceClassification"},
     executablePointers |-> {"formal/structures/QualityHierarchy/refinement/QualityHierarchyImplRefinesSpec.tla", "formal/structures/QualityHierarchy/refinement/QualityHierarchyImplRefinesSpec_Proof.tla", "crate://automation-structures/0.2.3/src/primitives/quality_hierarchy.rs", "formal/structures/QualityHierarchy/QualityHierarchy.tla", "formal/structures/QualityHierarchy/QualityHierarchy_Proof.tla"},
     libraryPremises |-> {"QualityHierarchy-written-contract-refinement-profile", "canonical-quality-hierarchy-machine", "QualityHierarchy-Safety", "ObligationPreservation", "CheckActStability", "OwnershipAssuranceClassification"},
     deploymentPremises |-> {"MaxLevelType", "NotANode", "finite-node-universe", "serialized-hierarchy-mutation", "atomic-edge-parent-commit"},
     residuals |-> {"formal-correspondence-is-limited-to-the-written-state-action-and-premise-map", "no-global-rootedness-or-connectivity-result", "no-completeness-or-balancing-result", "no-durable-or-concurrent-hierarchy-protocol"},
     evidenceCeilings |-> {"implementation-refinement-covers-only-the-written-bounded-contract-profile", "TLAPS-proves-local-edge-order-and-projection-invariants", "Verus-proves-the-finite-vector-parent-representation", "strict-level-descent-implies-no-directed-cycle-only-inside-the-modeled-edge-relation"},
     validCases |-> {"add-ordered-child"},
     boundaryCases |-> {"set-isolated-properties"},
     misuseCases |-> {"non-descending-edge"},
     failureCases |-> {"torn-parent-edge"},
     globalAssumptions |-> GlobalModelingAssumptionNames,
     conformanceConditions |-> ConformanceConditions,
     applicableFamilies |-> {"obligation", "check-act", "ownership-assurance", "refinement"},
     dischargedFamilies |-> {"obligation", "check-act", "ownership-assurance", "refinement"},
     transferClasses |-> {"safety"},
     refinementStatus |-> "mechanized",
     witnessStates |-> {"isolated", "linked", "invalid-edge"},
     witnessInitial |-> {"isolated"},
     witnessObligationStates |-> {"isolated", "linked"},
     witnessViolationStates |-> {"invalid-edge"},
     witnessSystemSteps |-> {<<"isolated", "linked">>, <<"isolated", "isolated">>},
     witnessEnvironmentSteps |-> {},
     witnessActionSteps |-> WitnessActionSteps,
     witnessRelySteps |-> {},
     witnessCommitSteps |-> {<<"isolated", "linked">>, <<"isolated", "isolated">>},
     witnessFailureSteps |-> {},
     witnessInterferenceSteps |-> {},
     witnessCheckActMode |-> "atomic",
     witnessCheckResultStates |-> {"isolated", "linked"},
     witnessPredicateStates |-> {"isolated", "linked"},
     witnessActors |-> {"hierarchy-claimant", "hierarchy-authority"},
     witnessProviders |-> {"hierarchy-authority"},
     witnessClaimant |-> "hierarchy-claimant",
     witnessCommitOwner |-> "hierarchy-authority",
     witnessCommitDelegate |-> "hierarchy-authority",
     witnessAssuranceProvider |-> "hierarchy-authority",
     witnessAssurancePosition |-> "at-commit",
     witnessPreventionControllers |-> {"hierarchy-authority"},
     witnessUnavailableProviders |-> {},
     witnessPersistentObserve |-> WitnessPersistentObserve,
     witnessPersistentEvidence |-> TRUE,
     witnessRecoveryAvailable |-> FALSE,
     witnessActiveStates |-> {"isolated", "linked"},
     witnessClosedStates |-> {},
     witnessProgressSteps |-> {},
     witnessOtherSteps |-> {},
     witnessHandoffSteps |-> {},
     witnessRankBound |-> 0,
     witnessRank |-> WitnessRank,
     witnessFairnessOwners |-> {"hierarchy-authority"},
     witnessFairnessOwner |-> "hierarchy-authority",
     witnessFairnessOwnerOf |-> WitnessFairnessOwnerOf]

====
