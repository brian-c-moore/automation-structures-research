---- MODULE EquivalenceClassDerivationData ----
EXTENDS StructureDerivationSchema

\* Generated from the checked derivation record. Do not edit by hand.

ImplementationStateMap ==
    [key \in {"n", "parent", "rank", "size", "ops_done", "max_ops", "max_rank"} |->
        CASE key = "n" -> "num_elements"
          [] key = "parent" -> "parent"
          [] key = "rank" -> "rnk"
          [] key = "size" -> "size"
          [] key = "ops_done" -> "ops_done"
          [] key = "max_ops" -> "max_ops"
          [] key = "max_rank" -> "max_rank"
          [] OTHER -> "max_rank"]

ObservationMap ==
    [key \in {"n", "parent", "rank", "size", "ops_done", "max_ops", "max_rank"} |->
        CASE key = "n" -> "num_elements"
          [] key = "parent" -> "parent"
          [] key = "rank" -> "rnk"
          [] key = "size" -> "size"
          [] key = "ops_done" -> "ops_done"
          [] key = "max_ops" -> "max_ops"
          [] key = "max_rank" -> "max_rank"
          [] OTHER -> "max_rank"]

ActionMap ==
    [key \in {"Union", "Idle"} |->
        CASE key = "Union" -> {"union"}
          [] key = "Idle" -> {"union"}
          [] OTHER -> {"union"}]

ViolationOf ==
    [key \in {"RepresentativeIdempotence", "RankMonotonicity", "RepresentativeRootedness"} |->
        CASE key = "RepresentativeIdempotence" -> "UnstableRepresentative"
          [] key = "RankMonotonicity" -> "RankOrderViolation"
          [] key = "RepresentativeRootedness" -> "UnrootedRepresentative"
          [] OTHER -> "UnrootedRepresentative"]

OwnerOf ==
    [key \in {"Union", "Idle"} |->
        CASE key = "Union" -> "union-find-authority"
          [] key = "Idle" -> "union-find-authority"
          [] OTHER -> "union-find-authority"]

DelegateOf ==
    [key \in {"Union", "Idle"} |->
        CASE key = "Union" -> {"union-find-authority"}
          [] key = "Idle" -> {"union-find-authority"}
          [] OTHER -> {"union-find-authority"}]

AssuranceAt ==
    [key \in {"Union"} |->
        CASE key = "Union" -> "at-commit"
          [] OTHER -> "at-commit"]

WitnessPersistentObserve ==
    [key \in {"separate", "merged", "invalid-forest"} |->
        CASE key = "separate" -> TRUE
          [] key = "merged" -> TRUE
          [] key = "invalid-forest" -> FALSE
          [] OTHER -> FALSE]

WitnessRank ==
    [key \in {"separate", "merged", "invalid-forest"} |->
        CASE key = "separate" -> 0
          [] key = "merged" -> 0
          [] key = "invalid-forest" -> 0
          [] OTHER -> 0]

WitnessFairnessOwnerOf == [key \in {} |-> "unused"]

WitnessActionSteps ==
    [key \in {"Union", "Idle"} |->
        CASE key = "Union" -> {<<"separate", "merged">>}
          [] key = "Idle" -> {<<"merged", "merged">>}
          [] OTHER -> {<<"merged", "merged">>}]

Derivation ==
    [structure |-> "EquivalenceClass",
     kind |-> "named-composition",
     propertyClasses |-> {"safety"},
     stateFields |-> {"num_elements", "max_ops", "parent", "rnk", "size", "ops_done", "max_rank"},
     observationFields |-> {"n", "parent", "rank", "size", "ops_done", "max_ops", "max_rank"},
     implementationStateFields |-> {"n", "parent", "rank", "size", "ops_done", "max_ops", "max_rank"},
     implementationStateMap |-> ImplementationStateMap,
     observationMap |-> ObservationMap,
     canonicalActions |-> {"Union", "Idle"},
     systemActions |-> {"Union", "Idle"},
     environmentActions |-> {},
     failureActions |-> {},
     commitActions |-> {"Union"},
     executableActions |-> {"union"},
     actionMap |-> ActionMap,
     obligations |-> {"RepresentativeIdempotence", "RankMonotonicity", "RepresentativeRootedness"},
     violations |-> {"UnstableRepresentative", "RankOrderViolation", "UnrootedRepresentative"},
     violationOf |-> ViolationOf,
     actors |-> {"class-claimant", "union-find-authority"},
     claimant |-> "class-claimant",
     ownerOf |-> OwnerOf,
     delegateOf |-> DelegateOf,
     assuranceAt |-> AssuranceAt,
     relies |-> {"finite-element-domain", "bounded-successful-union-count", "serialized-parent-rank-mutation"},
     guarantees |-> {"equivalenceclass-written-profile-refinement", "union-find-structural-safety", "atomic-union-license", "union-find-owner-ceiling"},
     runtimeProviders |-> {"union-find-authority", "finite-index-provider", "exclusive-mutation-provider"},
     failureCeilings |-> {"no-modeled-crash-or-torn-union", "concurrent-bypass-writer-outside-boundary", "bounded-union-by-rank-without-path-compression"},
     executionCarriers |-> {"Sequential"},
     localTheorems |-> {"EquivalenceClassImplRefinesSpec_Proof!RefinementThm", "EquivalenceClass_Proof!Safety", "EquivalenceClass_Proof!RepresentativeIdempotenceSafety", "EquivalenceClass_Proof!RankMonotonicitySafety", "EquivalenceClass_Proof!RepresentativeRootednessSafety", "TheoryKernel_Proof!ObligationPreservation", "TheoryKernel_Proof!CheckActStability", "OwnershipAssuranceKernel_Proof!OwnershipAssuranceClassification"},
     executablePointers |-> {"formal/structures/EquivalenceClass/refinement/EquivalenceClassImplRefinesSpec.tla", "formal/structures/EquivalenceClass/refinement/EquivalenceClassImplRefinesSpec_Proof.tla", "development-copy://automation-structures/0.3.2/src/compositions/equivalence_class.rs", "formal/structures/EquivalenceClass/EquivalenceClass.tla", "formal/structures/EquivalenceClass/EquivalenceClass_Proof.tla"},
     libraryPremises |-> {"EquivalenceClass-written-contract-refinement-profile", "canonical-bounded-union-find-machine", "EquivalenceClass-Safety", "ObligationPreservation", "CheckActStability", "OwnershipAssuranceClassification"},
     deploymentPremises |-> {"MaxOpsType", "finite-element-domain", "bounded-successful-union-count", "serialized-parent-rank-mutation"},
     residuals |-> {"formal-correspondence-is-limited-to-the-written-state-action-and-premise-map", "automation-structures-0.2.3-does-not-expose-the-written-profile-size-or-max-rank-state", "no-runtime-complexity-result", "no-path-compression-model", "symmetry-and-transitivity-are-equality-consequences-not-independent-controlled-obligations"},
     evidenceCeilings |-> {"implementation-refinement-covers-only-the-written-bounded-contract-profile", "TLAPS-proves-the-bounded-union-by-rank-forest", "Verus-proves-exact-success-and-rejection-parent-rank-and-budget-effects-for-the-executable-state", "the-fixed-known-answer-vectors-are-not-an-exhaustive-input-proof", "no-lock-free-concurrent-union-find-claim"},
     validCases |-> {"merge-distinct-classes"},
     boundaryCases |-> {"operation-bound-idle"},
     misuseCases |-> {"parent-to-lower-rank"},
     failureCases |-> {"torn-union"},
     globalAssumptions |-> GlobalModelingAssumptionNames,
     conformanceConditions |-> ConformanceConditions,
     applicableFamilies |-> {"obligation", "check-act", "ownership-assurance", "refinement"},
     dischargedFamilies |-> {"obligation", "check-act", "ownership-assurance", "refinement"},
     transferClasses |-> {"safety"},
     refinementStatus |-> "mechanized",
     witnessStates |-> {"separate", "merged", "invalid-forest"},
     witnessInitial |-> {"separate"},
     witnessObligationStates |-> {"separate", "merged"},
     witnessViolationStates |-> {"invalid-forest"},
     witnessSystemSteps |-> {<<"separate", "merged">>, <<"merged", "merged">>},
     witnessEnvironmentSteps |-> {},
     witnessActionSteps |-> WitnessActionSteps,
     witnessRelySteps |-> {},
     witnessCommitSteps |-> {<<"separate", "merged">>},
     witnessFailureSteps |-> {},
     witnessInterferenceSteps |-> {},
     witnessCheckActMode |-> "atomic",
     witnessCheckResultStates |-> {"separate", "merged"},
     witnessPredicateStates |-> {"separate", "merged"},
     witnessActors |-> {"class-claimant", "union-find-authority"},
     witnessProviders |-> {"union-find-authority"},
     witnessClaimant |-> "class-claimant",
     witnessCommitOwner |-> "union-find-authority",
     witnessCommitDelegate |-> "union-find-authority",
     witnessAssuranceProvider |-> "union-find-authority",
     witnessAssurancePosition |-> "at-commit",
     witnessPreventionControllers |-> {"union-find-authority"},
     witnessUnavailableProviders |-> {},
     witnessPersistentObserve |-> WitnessPersistentObserve,
     witnessPersistentEvidence |-> TRUE,
     witnessRecoveryAvailable |-> FALSE,
     witnessActiveStates |-> {"separate", "merged"},
     witnessClosedStates |-> {},
     witnessProgressSteps |-> {},
     witnessOtherSteps |-> {},
     witnessHandoffSteps |-> {},
     witnessRankBound |-> 0,
     witnessRank |-> WitnessRank,
     witnessFairnessOwners |-> {"union-find-authority"},
     witnessFairnessOwner |-> "union-find-authority",
     witnessFairnessOwnerOf |-> WitnessFairnessOwnerOf]

====
