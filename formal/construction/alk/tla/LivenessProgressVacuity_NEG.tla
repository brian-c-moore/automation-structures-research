---- MODULE LivenessProgressVacuity_NEG ----
EXTENDS ALKSemanticModelWitness

EmptyLivenessProgressActions ==
    [obligation \in Obligations |->
        IF ObligationPropertyClass[obligation] = "liveness"
          THEN {}
        ELSE LivenessProgressActions[obligation]]

AllLivenessOtherActions ==
    [obligation \in Obligations |->
        IF ObligationPropertyClass[obligation] = "liveness"
          THEN ActionLabels
        ELSE LivenessOtherActions[obligation]]

LivenessProgressBoundaryHeld ==
    SelectedObligationBoundaryTyped(
        States, ActionLabels, Actions, Claims, Obligations, Actors,
        ObligationPropertyClass,
        ClaimObligations, ObligationStates, ViolationStates,
        AllowedRelationSteps, ViolatingActions,
        DerivedFrom,
        LivenessActiveStates, LivenessClosedStates,
        EmptyLivenessProgressActions, AllLivenessOtherActions,
        LivenessWeakFairProgressActions,
        LivenessRankBound, LivenessRank,
        LivenessFairnessOwner, LivenessFairnessOwnerOf)

NegativeControlExpected == NegativeControlGate(LivenessProgressBoundaryHeld)

====
