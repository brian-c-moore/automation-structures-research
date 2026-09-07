---- MODULE BacktrackingTraversalDerivationData ----
EXTENDS StructureDerivationSchema

\* Generated from the checked derivation record. Do not edit by hand.

ImplementationStateMap ==
    [key \in {"path", "aux", "ledger", "visited"} |->
        CASE key = "path" -> "path"
          [] key = "aux" -> "aux"
          [] key = "ledger" -> "ledger"
          [] key = "visited" -> "visited"
          [] OTHER -> "visited"]

ObservationMap ==
    [key \in {"path", "aux", "ledger", "visited"} |->
        CASE key = "path" -> "path"
          [] key = "aux" -> "aux"
          [] key = "ledger" -> "ledger"
          [] key = "visited" -> "visited"
          [] OTHER -> "visited"]

ActionMap ==
    [key \in {"Descend", "Visit", "Ascend"} |->
        CASE key = "Descend" -> {"descend"}
          [] key = "Visit" -> {"visit"}
          [] key = "Ascend" -> {"ascend"}
          [] OTHER -> {"ascend"}]

ViolationOf ==
    [key \in {"Pairing", "StateRestoration", "RecordedLeafValidity"} |->
        CASE key = "Pairing" -> "UnpairedMutation"
          [] key = "StateRestoration" -> "BrokenRestorationChain"
          [] key = "RecordedLeafValidity" -> "InvalidRecordedLeaf"
          [] OTHER -> "InvalidRecordedLeaf"]

OwnerOf ==
    [key \in {"Descend", "Visit", "Ascend"} |->
        CASE key = "Descend" -> "backtracking-authority"
          [] key = "Visit" -> "backtracking-authority"
          [] key = "Ascend" -> "backtracking-authority"
          [] OTHER -> "backtracking-authority"]

DelegateOf ==
    [key \in {"Descend", "Visit", "Ascend"} |->
        CASE key = "Descend" -> {"backtracking-authority"}
          [] key = "Visit" -> {"backtracking-authority"}
          [] key = "Ascend" -> {"backtracking-authority"}
          [] OTHER -> {"backtracking-authority"}]

AssuranceAt ==
    [key \in {"Descend", "Visit", "Ascend"} |->
        CASE key = "Descend" -> "at-commit"
          [] key = "Visit" -> "at-commit"
          [] key = "Ascend" -> "at-commit"
          [] OTHER -> "at-commit"]

WitnessPersistentObserve ==
    [key \in {"root", "descended", "broken-restoration"} |->
        CASE key = "root" -> TRUE
          [] key = "descended" -> TRUE
          [] key = "broken-restoration" -> FALSE
          [] OTHER -> FALSE]

WitnessRank ==
    [key \in {"root", "descended", "broken-restoration"} |->
        CASE key = "root" -> 0
          [] key = "descended" -> 0
          [] key = "broken-restoration" -> 0
          [] OTHER -> 0]

WitnessFairnessOwnerOf == [key \in {} |-> "unused"]

WitnessActionSteps ==
    [key \in {"Descend", "Visit", "Ascend"} |->
        CASE key = "Descend" -> {<<"root", "descended">>}
          [] key = "Visit" -> {<<"descended", "descended">>}
          [] key = "Ascend" -> {<<"descended", "root">>}
          [] OTHER -> {<<"descended", "root">>}]

Derivation ==
    [structure |-> "BacktrackingTraversal",
     kind |-> "abstraction-primitive",
     propertyClasses |-> {"safety"},
     stateFields |-> {"path", "aux", "ledger", "visited"},
     observationFields |-> {"path", "aux", "ledger", "visited"},
     implementationStateFields |-> {"path", "aux", "ledger", "visited"},
     implementationStateMap |-> ImplementationStateMap,
     observationMap |-> ObservationMap,
     canonicalActions |-> {"Descend", "Visit", "Ascend"},
     systemActions |-> {"Descend", "Visit", "Ascend"},
     environmentActions |-> {},
     failureActions |-> {},
     commitActions |-> {"Descend", "Visit", "Ascend"},
     executableActions |-> {"descend", "visit", "ascend"},
     actionMap |-> ActionMap,
     obligations |-> {"Pairing", "StateRestoration", "RecordedLeafValidity"},
     violations |-> {"UnpairedMutation", "BrokenRestorationChain", "InvalidRecordedLeaf"},
     violationOf |-> ViolationOf,
     actors |-> {"traversal-claimant", "backtracking-authority", "mutation-algebra-provider"},
     claimant |-> "traversal-claimant",
     ownerOf |-> OwnerOf,
     delegateOf |-> DelegateOf,
     assuranceAt |-> AssuranceAt,
     relies |-> {"finite-bounded-decision-tree", "mutate-closure-and-undo-round-trip", "serialized-path-ledger-aux-mutation"},
     guarantees |-> {"backtrackingtraversal-written-profile-refinement", "paired-restoration-safety", "atomic-do-undo-license", "backtracking-owner-ceiling"},
     runtimeProviders |-> {"backtracking-authority", "mutation-algebra-provider", "exclusive-mutation-provider"},
     failureCeilings |-> {"no-modeled-crash-or-partial-token-write", "unpaired-external-aux-mutation-outside-boundary", "finite-bounded-tree-only"},
     executionCarriers |-> {"Sequential"},
     localTheorems |-> {"BacktrackingTraversalImplRefinesSpec_Proof!RefinementThm", "BacktrackingTraversalUndo_Proof!Safety", "BacktrackingTraversalUndo_Proof!PairingSafety", "BacktrackingTraversalUndo_Proof!StateRestorationSafety", "BacktrackingTraversalUndo_Proof!RecordedLeafValiditySafety", "TheoryKernel_Proof!ObligationPreservation", "TheoryKernel_Proof!CheckActStability", "OwnershipAssuranceKernel_Proof!OwnershipAssuranceClassification"},
     executablePointers |-> {"formal/structures/BacktrackingTraversal/refinement/BacktrackingTraversalImplRefinesSpec.tla", "formal/structures/BacktrackingTraversal/refinement/BacktrackingTraversalImplRefinesSpec_Proof.tla", "crate://automation-structures/0.2.3/src/primitives/backtracking_traversal.rs", "formal/structures/BacktrackingTraversal/BacktrackingTraversalUndo.tla", "formal/structures/BacktrackingTraversal/BacktrackingTraversalUndo_Proof.tla"},
     libraryPremises |-> {"BacktrackingTraversal-written-contract-refinement-profile", "canonical-paired-do-undo-machine", "BacktrackingTraversalUndo-Safety", "ObligationPreservation", "CheckActStability", "OwnershipAssuranceClassification"},
     deploymentPremises |-> {"BranchFactorType", "MaxDepthType", "InitAuxType", "MutateClosed", "UndoInverts", "serialized-path-ledger-aux-mutation"},
     residuals |-> {"formal-correspondence-is-limited-to-the-written-state-action-and-premise-map", "no-full-leaf-coverage-result", "no-scheduler-order-result", "no-general-graph-search-completeness"},
     evidenceCeilings |-> {"implementation-refinement-covers-only-the-written-bounded-contract-profile", "TLAPS-proves-paired-do-undo-safety-under-an-abstract-round-trip-law", "Verus-proves-the-written-modulo-three-executable-carrier", "RecordedLeafValiditySafety-validates-recorded-leaves-only"},
     validCases |-> {"descend-visit-ascend"},
     boundaryCases |-> {"root-and-max-depth"},
     misuseCases |-> {"unpaired-aux-mutation"},
     failureCases |-> {"partial-undo-token"},
     globalAssumptions |-> GlobalModelingAssumptionNames,
     conformanceConditions |-> ConformanceConditions,
     applicableFamilies |-> {"obligation", "check-act", "ownership-assurance", "refinement"},
     dischargedFamilies |-> {"obligation", "check-act", "ownership-assurance", "refinement"},
     transferClasses |-> {"safety"},
     refinementStatus |-> "mechanized",
     witnessStates |-> {"root", "descended", "broken-restoration"},
     witnessInitial |-> {"root"},
     witnessObligationStates |-> {"root", "descended"},
     witnessViolationStates |-> {"broken-restoration"},
     witnessSystemSteps |-> {<<"root", "descended">>, <<"descended", "descended">>, <<"descended", "root">>},
     witnessEnvironmentSteps |-> {},
     witnessActionSteps |-> WitnessActionSteps,
     witnessRelySteps |-> {},
     witnessCommitSteps |-> {<<"root", "descended">>, <<"descended", "descended">>, <<"descended", "root">>},
     witnessFailureSteps |-> {},
     witnessInterferenceSteps |-> {},
     witnessCheckActMode |-> "atomic",
     witnessCheckResultStates |-> {"root", "descended"},
     witnessPredicateStates |-> {"root", "descended"},
     witnessActors |-> {"traversal-claimant", "backtracking-authority", "mutation-algebra-provider"},
     witnessProviders |-> {"backtracking-authority", "mutation-algebra-provider"},
     witnessClaimant |-> "traversal-claimant",
     witnessCommitOwner |-> "backtracking-authority",
     witnessCommitDelegate |-> "backtracking-authority",
     witnessAssuranceProvider |-> "backtracking-authority",
     witnessAssurancePosition |-> "at-commit",
     witnessPreventionControllers |-> {"backtracking-authority"},
     witnessUnavailableProviders |-> {},
     witnessPersistentObserve |-> WitnessPersistentObserve,
     witnessPersistentEvidence |-> TRUE,
     witnessRecoveryAvailable |-> FALSE,
     witnessActiveStates |-> {"root", "descended"},
     witnessClosedStates |-> {},
     witnessProgressSteps |-> {},
     witnessOtherSteps |-> {},
     witnessHandoffSteps |-> {},
     witnessRankBound |-> 0,
     witnessRank |-> WitnessRank,
     witnessFairnessOwners |-> {"backtracking-authority"},
     witnessFairnessOwner |-> "backtracking-authority",
     witnessFairnessOwnerOf |-> WitnessFairnessOwnerOf]

====
