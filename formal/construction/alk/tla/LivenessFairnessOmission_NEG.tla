---- MODULE LivenessFairnessOmission_NEG ----
EXTENDS ALKSemanticModelWitness

MissingWeakFairProgressActions ==
    [obligation \in Obligations |->
        IF ObligationPropertyClass[obligation] = "liveness"
          THEN {}
        ELSE LivenessWeakFairProgressActions[obligation]]

LivenessFairnessBoundaryHeld ==
    SelectedObligationBoundaryTyped(
        States, ActionLabels, Actions, Claims, Obligations, Actors,
        ObligationPropertyClass,
        ClaimObligations, ObligationStates, ViolationStates,
        AllowedRelationSteps, ViolatingActions,
        DerivedFrom,
        LivenessActiveStates, LivenessClosedStates,
        LivenessProgressActions, LivenessOtherActions,
        MissingWeakFairProgressActions,
        LivenessRankBound, LivenessRank,
        LivenessFairnessOwner, LivenessFairnessOwnerOf)

NegativeControlExpected == NegativeControlGate(LivenessFairnessBoundaryHeld)

====
