---- MODULE CompetitiveSelectionDerivationData ----
EXTENDS StructureDerivationSchema

\* Generated from the checked derivation record. Do not edit by hand.

ImplementationStateMap ==
    [key \in {"hard_num_seats", "hard_num_candidates", "hard_max_score", "hard_allocation", "hard_scores", "soft_weight_total", "soft_max_score", "soft_scores", "soft_extra", "mutable_weight_total", "mutable_max_score", "mutable_scores", "mutable_extra", "ranked_k", "ranked_max_score", "ranked_selected", "ranked_scores"} |->
        CASE key = "hard_num_seats" -> "hard_num_seats"
          [] key = "hard_num_candidates" -> "hard_num_candidates"
          [] key = "hard_max_score" -> "hard_max_score"
          [] key = "hard_allocation" -> "hard_allocation"
          [] key = "hard_scores" -> "hard_scores"
          [] key = "soft_weight_total" -> "soft_weight_total"
          [] key = "soft_max_score" -> "soft_max_score"
          [] key = "soft_scores" -> "soft_scores"
          [] key = "soft_extra" -> "soft_extra"
          [] key = "mutable_weight_total" -> "mutable_weight_total"
          [] key = "mutable_max_score" -> "mutable_max_score"
          [] key = "mutable_scores" -> "mutable_scores"
          [] key = "mutable_extra" -> "mutable_extra"
          [] key = "ranked_k" -> "ranked_k"
          [] key = "ranked_max_score" -> "ranked_max_score"
          [] key = "ranked_selected" -> "ranked_selected"
          [] key = "ranked_scores" -> "ranked_scores"
          [] OTHER -> "ranked_scores"]

ObservationMap ==
    [key \in {"hard_num_seats", "hard_num_candidates", "hard_max_score", "hard_allocation", "hard_scores", "soft_weight_total", "soft_max_score", "soft_scores", "soft_extra", "mutable_weight_total", "mutable_max_score", "mutable_scores", "mutable_extra", "ranked_k", "ranked_max_score", "ranked_selected", "ranked_scores"} |->
        CASE key = "hard_num_seats" -> "hard_num_seats"
          [] key = "hard_num_candidates" -> "hard_num_candidates"
          [] key = "hard_max_score" -> "hard_max_score"
          [] key = "hard_allocation" -> "hard_allocation"
          [] key = "hard_scores" -> "hard_scores"
          [] key = "soft_weight_total" -> "soft_weight_total"
          [] key = "soft_max_score" -> "soft_max_score"
          [] key = "soft_scores" -> "soft_scores"
          [] key = "soft_extra" -> "soft_extra"
          [] key = "mutable_weight_total" -> "mutable_weight_total"
          [] key = "mutable_max_score" -> "mutable_max_score"
          [] key = "mutable_scores" -> "mutable_scores"
          [] key = "mutable_extra" -> "mutable_extra"
          [] key = "ranked_k" -> "ranked_k"
          [] key = "ranked_max_score" -> "ranked_max_score"
          [] key = "ranked_selected" -> "ranked_selected"
          [] key = "ranked_scores" -> "ranked_scores"
          [] OTHER -> "ranked_scores"]

ActionMap ==
    [key \in {"RankedSelect", "RankedUpdateScores", "HardEvaluate", "HardUpdateScore", "SoftAssignNext", "MutableAssignNext", "MutableUpdateScore"} |->
        CASE key = "RankedSelect" -> {"CompetitiveSelectionRanked::select"}
          [] key = "RankedUpdateScores" -> {"CompetitiveSelectionRanked::update_scores"}
          [] key = "HardEvaluate" -> {"CompetitiveSelectionHardExclusive::evaluate"}
          [] key = "HardUpdateScore" -> {"CompetitiveSelectionHardExclusive::update_score"}
          [] key = "SoftAssignNext" -> {"CompetitiveSelectionSoft::assign_next"}
          [] key = "MutableAssignNext" -> {"CompetitiveSelectionSoft::assign_next"}
          [] key = "MutableUpdateScore" -> {"CompetitiveSelectionSoft::update_score"}
          [] OTHER -> {"CompetitiveSelectionSoft::update_score"}]

ViolationOf ==
    [key \in {"RankedBoundedMultiplicity", "RankedThresholdOptimality", "RankedTieBreak", "HardMutualExclusion", "HardWinnerOptimality", "HardWinnerTieBreak", "SoftNonNegativity", "SoftBoundedTotal", "SoftNormalization", "SoftUniversalContribution", "SoftScoreOrderPreservation", "SoftTieBoundedness"} |->
        CASE key = "RankedBoundedMultiplicity" -> "RankedTooManyWinners"
          [] key = "RankedThresholdOptimality" -> "RankedSuboptimalWinner"
          [] key = "RankedTieBreak" -> "RankedTieBreakViolation"
          [] key = "HardMutualExclusion" -> "HardDuplicateWinner"
          [] key = "HardWinnerOptimality" -> "HardSuboptimalAvailableWinner"
          [] key = "HardWinnerTieBreak" -> "HardTieBreakViolation"
          [] key = "SoftNonNegativity" -> "SoftNegativeWeight"
          [] key = "SoftBoundedTotal" -> "SoftTotalOvershoot"
          [] key = "SoftNormalization" -> "SoftTerminalNonNormalization"
          [] key = "SoftUniversalContribution" -> "SoftZeroContribution"
          [] key = "SoftScoreOrderPreservation" -> "SoftScoreOrderViolation"
          [] key = "SoftTieBoundedness" -> "SoftTieSpreadViolation"
          [] OTHER -> "SoftTieSpreadViolation"]

OwnerOf ==
    [key \in {"RankedSelect", "RankedUpdateScores", "HardEvaluate", "HardUpdateScore", "SoftAssignNext", "MutableAssignNext", "MutableUpdateScore"} |->
        CASE key = "RankedSelect" -> "selection-authority"
          [] key = "RankedUpdateScores" -> "score-provider"
          [] key = "HardEvaluate" -> "selection-authority"
          [] key = "HardUpdateScore" -> "score-provider"
          [] key = "SoftAssignNext" -> "selection-authority"
          [] key = "MutableAssignNext" -> "selection-authority"
          [] key = "MutableUpdateScore" -> "score-provider"
          [] OTHER -> "score-provider"]

DelegateOf ==
    [key \in {"RankedSelect", "RankedUpdateScores", "HardEvaluate", "HardUpdateScore", "SoftAssignNext", "MutableAssignNext", "MutableUpdateScore"} |->
        CASE key = "RankedSelect" -> {"selection-authority"}
          [] key = "RankedUpdateScores" -> {"score-provider"}
          [] key = "HardEvaluate" -> {"selection-authority"}
          [] key = "HardUpdateScore" -> {"score-provider"}
          [] key = "SoftAssignNext" -> {"selection-authority"}
          [] key = "MutableAssignNext" -> {"selection-authority"}
          [] key = "MutableUpdateScore" -> {"score-provider"}
          [] OTHER -> {"score-provider"}]

AssuranceAt ==
    [key \in {"RankedSelect", "HardEvaluate", "SoftAssignNext", "MutableAssignNext"} |->
        CASE key = "RankedSelect" -> "at-commit"
          [] key = "HardEvaluate" -> "at-commit"
          [] key = "SoftAssignNext" -> "at-commit"
          [] key = "MutableAssignNext" -> "at-commit"
          [] OTHER -> "at-commit"]

WitnessPersistentObserve ==
    [key \in {"scores-ready", "ranked-selected", "hard-assigned", "soft-partial", "invalid-selection"} |->
        CASE key = "scores-ready" -> TRUE
          [] key = "ranked-selected" -> TRUE
          [] key = "hard-assigned" -> TRUE
          [] key = "soft-partial" -> TRUE
          [] key = "invalid-selection" -> FALSE
          [] OTHER -> FALSE]

WitnessRank ==
    [key \in {"scores-ready", "ranked-selected", "hard-assigned", "soft-partial", "invalid-selection"} |->
        CASE key = "scores-ready" -> 0
          [] key = "ranked-selected" -> 0
          [] key = "hard-assigned" -> 0
          [] key = "soft-partial" -> 0
          [] key = "invalid-selection" -> 0
          [] OTHER -> 0]

WitnessFairnessOwnerOf == [key \in {} |-> "unused"]

WitnessActionSteps ==
    [key \in {"RankedSelect", "RankedUpdateScores", "HardEvaluate", "HardUpdateScore", "SoftAssignNext", "MutableAssignNext", "MutableUpdateScore"} |->
        CASE key = "RankedSelect" -> {<<"scores-ready", "ranked-selected">>}
          [] key = "RankedUpdateScores" -> {<<"ranked-selected", "scores-ready">>}
          [] key = "HardEvaluate" -> {<<"scores-ready", "hard-assigned">>}
          [] key = "HardUpdateScore" -> {<<"hard-assigned", "scores-ready">>}
          [] key = "SoftAssignNext" -> {<<"scores-ready", "soft-partial">>}
          [] key = "MutableAssignNext" -> {<<"scores-ready", "soft-partial">>}
          [] key = "MutableUpdateScore" -> {<<"soft-partial", "scores-ready">>}
          [] OTHER -> {<<"soft-partial", "scores-ready">>}]

Derivation ==
    [structure |-> "CompetitiveSelection",
     kind |-> "abstraction-primitive",
     propertyClasses |-> {"safety"},
     stateFields |-> {"hard_num_seats", "hard_num_candidates", "hard_max_score", "hard_allocation", "hard_scores", "soft_weight_total", "soft_max_score", "soft_scores", "soft_extra", "mutable_weight_total", "mutable_max_score", "mutable_scores", "mutable_extra", "ranked_k", "ranked_max_score", "ranked_selected", "ranked_scores"},
     observationFields |-> {"hard_num_seats", "hard_num_candidates", "hard_max_score", "hard_allocation", "hard_scores", "soft_weight_total", "soft_max_score", "soft_scores", "soft_extra", "mutable_weight_total", "mutable_max_score", "mutable_scores", "mutable_extra", "ranked_k", "ranked_max_score", "ranked_selected", "ranked_scores"},
     implementationStateFields |-> {"hard_num_seats", "hard_num_candidates", "hard_max_score", "hard_allocation", "hard_scores", "soft_weight_total", "soft_max_score", "soft_scores", "soft_extra", "mutable_weight_total", "mutable_max_score", "mutable_scores", "mutable_extra", "ranked_k", "ranked_max_score", "ranked_selected", "ranked_scores"},
     implementationStateMap |-> ImplementationStateMap,
     observationMap |-> ObservationMap,
     canonicalActions |-> {"RankedSelect", "RankedUpdateScores", "HardEvaluate", "HardUpdateScore", "SoftAssignNext", "MutableAssignNext", "MutableUpdateScore"},
     systemActions |-> {"RankedSelect", "HardEvaluate", "SoftAssignNext", "MutableAssignNext"},
     environmentActions |-> {"RankedUpdateScores", "HardUpdateScore", "MutableUpdateScore"},
     failureActions |-> {},
     commitActions |-> {"RankedSelect", "HardEvaluate", "SoftAssignNext", "MutableAssignNext"},
     executableActions |-> {"CompetitiveSelectionRanked::select", "CompetitiveSelectionRanked::update_scores", "CompetitiveSelectionHardExclusive::evaluate", "CompetitiveSelectionHardExclusive::update_score", "CompetitiveSelectionSoft::assign_next", "CompetitiveSelectionSoft::update_score"},
     actionMap |-> ActionMap,
     obligations |-> {"RankedBoundedMultiplicity", "RankedThresholdOptimality", "RankedTieBreak", "HardMutualExclusion", "HardWinnerOptimality", "HardWinnerTieBreak", "SoftNonNegativity", "SoftBoundedTotal", "SoftNormalization", "SoftUniversalContribution", "SoftScoreOrderPreservation", "SoftTieBoundedness"},
     violations |-> {"RankedTooManyWinners", "RankedSuboptimalWinner", "RankedTieBreakViolation", "HardDuplicateWinner", "HardSuboptimalAvailableWinner", "HardTieBreakViolation", "SoftNegativeWeight", "SoftTotalOvershoot", "SoftTerminalNonNormalization", "SoftZeroContribution", "SoftScoreOrderViolation", "SoftTieSpreadViolation"},
     violationOf |-> ViolationOf,
     actors |-> {"selection-claimant", "selection-authority", "score-provider"},
     claimant |-> "selection-claimant",
     ownerOf |-> OwnerOf,
     delegateOf |-> DelegateOf,
     assuranceAt |-> AssuranceAt,
     relies |-> {"finite-candidate-and-seat-domains", "serialized-variant-state-mutation", "atomic-selection-or-award-commit", "score-writers-reset-dependent-selection-state"},
     guarantees |-> {"competitiveselection-hard-written-profile-refinement", "competitiveselection-soft-written-profile-refinement", "competitiveselection-mutable-written-profile-refinement", "competitiveselection-ranked-written-profile-refinement", "ranked-top-k-safety", "hard-exclusive-winner-safety", "soft-discrete-apportionment-safety", "atomic-selection-license", "selection-owner-ceiling"},
     runtimeProviders |-> {"selection-authority", "score-provider", "finite-enumeration-provider"},
     failureCeilings |-> {"no-modeled-crash-or-torn-selection", "concurrent-staged-winner-outside-boundary", "score-update-without-required-reset-outside-rely"},
     executionCarriers |-> {"Sequential"},
     localTheorems |-> {"CompetitiveSelectionImplRefinesSpec_Proof!HardRefinementThm", "CompetitiveSelectionImplRefinesSpec_Proof!SoftRefinementThm", "CompetitiveSelectionImplRefinesSpec_Proof!MutableRefinementThm", "CompetitiveSelectionImplRefinesSpec_Proof!RankedRefinementThm", "CompetitiveSelectionRanked_Proof!Safety", "CompetitiveSelectionHardExclusive_Proof!Safety", "CompetitiveSelectionSoftMutableScores_Proof!MutableScoreSafety", "TheoryKernel_Proof!ObligationPreservation", "TheoryKernel_Proof!CheckActStability", "OwnershipAssuranceKernel_Proof!OwnershipAssuranceClassification"},
     executablePointers |-> {"formal/structures/CompetitiveSelection/refinement/CompetitiveSelectionImplRefinesSpec.tla", "formal/structures/CompetitiveSelection/refinement/CompetitiveSelectionImplRefinesSpec_Proof.tla", "formal/structures/CompetitiveSelection/refinement/CompetitiveSelectionImplRefinesSpec_NEG.tla", "formal/structures/CompetitiveSelection/refinement/CompetitiveSelectionSoftImplRefinesSpec_NEG.tla", "formal/structures/CompetitiveSelection/refinement/CompetitiveSelectionMutableImplRefinesSpec_NEG.tla", "formal/structures/CompetitiveSelection/refinement/CompetitiveSelectionRankedImplRefinesSpec_NEG.tla", "crate://automation-structures/0.2.3/src/primitives/competitive_selection.rs", "formal/structures/CompetitiveSelection/CompetitiveSelectionRanked.tla", "formal/structures/CompetitiveSelection/CompetitiveSelectionHardExclusive.tla", "formal/structures/CompetitiveSelection/CompetitiveSelectionSoftMutableScores.tla"},
     libraryPremises |-> {"CompetitiveSelection-written-contract-refinement-profile", "canonical-ranked-selection-machine", "canonical-hard-exclusive-selection-machine", "canonical-soft-mutable-score-machine", "three-canonical-selection-safety-theorems", "ObligationPreservation", "CheckActStability", "OwnershipAssuranceClassification"},
     deploymentPremises |-> {"finite-candidate-and-seat-domains", "variant-specific-score-and-weight-bounds", "stable-finite-enumeration-for-tie-breaks", "serialized-variant-state-mutation", "score-writers-reset-dependent-selection-state"},
     residuals |-> {"formal-correspondence-is-limited-to-the-written-state-action-and-premise-map", "no-cross-variant-equivalence-or-substitutability-theorem", "no-eventual-selection-or-coverage-result", "soft-carrier-is-discrete-Webster-apportionment-not-exact-softmax"},
     evidenceCeilings |-> {"implementation-refinement-covers-only-the-written-bounded-contract-profile", "TLAPS-separately-proves-all-three-canonical-carriers", "Verus-proves-the-three-written-variant-representations", "the-shared-record-is-a-tagged-family-contract-not-a-theorem-that-the-variants-are-equivalent"},
     validCases |-> {"variant-admitted-selection"},
     boundaryCases |-> {"score-update-reset"},
     misuseCases |-> {"mix-variant-contracts"},
     failureCases |-> {"split-observe-select"},
     globalAssumptions |-> GlobalModelingAssumptionNames,
     conformanceConditions |-> ConformanceConditions,
     applicableFamilies |-> {"obligation", "check-act", "ownership-assurance", "refinement"},
     dischargedFamilies |-> {"obligation", "check-act", "ownership-assurance", "refinement"},
     transferClasses |-> {"safety"},
     refinementStatus |-> "mechanized",
     witnessStates |-> {"scores-ready", "ranked-selected", "hard-assigned", "soft-partial", "invalid-selection"},
     witnessInitial |-> {"scores-ready"},
     witnessObligationStates |-> {"scores-ready", "ranked-selected", "hard-assigned", "soft-partial"},
     witnessViolationStates |-> {"invalid-selection"},
     witnessSystemSteps |-> {<<"scores-ready", "ranked-selected">>, <<"scores-ready", "hard-assigned">>, <<"scores-ready", "soft-partial">>},
     witnessEnvironmentSteps |-> {<<"ranked-selected", "scores-ready">>, <<"hard-assigned", "scores-ready">>, <<"soft-partial", "scores-ready">>},
     witnessActionSteps |-> WitnessActionSteps,
     witnessRelySteps |-> {<<"ranked-selected", "scores-ready">>, <<"hard-assigned", "scores-ready">>, <<"soft-partial", "scores-ready">>},
     witnessCommitSteps |-> {<<"scores-ready", "ranked-selected">>, <<"scores-ready", "hard-assigned">>, <<"scores-ready", "soft-partial">>},
     witnessFailureSteps |-> {},
     witnessInterferenceSteps |-> {},
     witnessCheckActMode |-> "atomic",
     witnessCheckResultStates |-> {"scores-ready", "ranked-selected", "hard-assigned", "soft-partial"},
     witnessPredicateStates |-> {"scores-ready", "ranked-selected", "hard-assigned", "soft-partial"},
     witnessActors |-> {"selection-claimant", "selection-authority", "score-provider"},
     witnessProviders |-> {"selection-authority", "score-provider"},
     witnessClaimant |-> "selection-claimant",
     witnessCommitOwner |-> "selection-authority",
     witnessCommitDelegate |-> "selection-authority",
     witnessAssuranceProvider |-> "selection-authority",
     witnessAssurancePosition |-> "at-commit",
     witnessPreventionControllers |-> {"selection-authority"},
     witnessUnavailableProviders |-> {},
     witnessPersistentObserve |-> WitnessPersistentObserve,
     witnessPersistentEvidence |-> TRUE,
     witnessRecoveryAvailable |-> FALSE,
     witnessActiveStates |-> {"scores-ready", "ranked-selected", "hard-assigned", "soft-partial"},
     witnessClosedStates |-> {},
     witnessProgressSteps |-> {},
     witnessOtherSteps |-> {},
     witnessHandoffSteps |-> {},
     witnessRankBound |-> 0,
     witnessRank |-> WitnessRank,
     witnessFairnessOwners |-> {"selection-authority"},
     witnessFairnessOwner |-> "selection-authority",
     witnessFairnessOwnerOf |-> WitnessFairnessOwnerOf]

====
