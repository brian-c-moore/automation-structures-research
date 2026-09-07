---- MODULE RelationalAllowanceVacuity_NEG ----
EXTENDS ALKSemanticModelWitness

EmptyRelationalAllowance ==
    [obligation \in Obligations |->
        IF ObligationPropertyClass[obligation] = "relational"
          THEN {}
        ELSE AllowedRelationSteps[obligation]]

EmptyAllowanceViolatingActions ==
    [obligation \in Obligations |->
        ExpectedViolatingActionsFor(
            obligation, States, ActionLabels, Actions,
            ObligationPropertyClass,
            ObligationStates, ViolationStates,
            EmptyRelationalAllowance)]

RelationalAllowanceInhabited ==
    SelectedObligationBoundaryTyped(
        States, ActionLabels, Actions, Claims, Obligations, Actors,
        ObligationPropertyClass,
        ClaimObligations, ObligationStates, ViolationStates,
        EmptyRelationalAllowance, EmptyAllowanceViolatingActions,
        DerivedFrom,
        LivenessActiveStates, LivenessClosedStates,
        LivenessProgressActions, LivenessOtherActions,
        LivenessWeakFairProgressActions,
        LivenessRankBound, LivenessRank,
        LivenessFairnessOwner, LivenessFairnessOwnerOf)

NegativeControlExpected == NegativeControlGate(RelationalAllowanceInhabited)

====
