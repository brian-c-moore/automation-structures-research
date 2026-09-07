---- MODULE ViolatingActionOmission_NEG ----
EXTENDS ALKSemanticModelWitness

OmittedViolatingActions ==
    [obligation \in Obligations |->
        ViolatingActions[obligation] \ {"audit-loss"}]

ExactViolatingActionInventory ==
    SelectedObligationBoundaryTyped(
        States, ActionLabels, Actions, Claims, Obligations, Actors,
        ObligationPropertyClass,
        ClaimObligations, ObligationStates, ViolationStates,
        AllowedRelationSteps, OmittedViolatingActions,
        DerivedFrom,
        LivenessActiveStates, LivenessClosedStates,
        LivenessProgressActions, LivenessOtherActions,
        LivenessWeakFairProgressActions,
        LivenessRankBound, LivenessRank,
        LivenessFairnessOwner, LivenessFairnessOwnerOf)

NegativeControlExpected == NegativeControlGate(ExactViolatingActionInventory)

====
