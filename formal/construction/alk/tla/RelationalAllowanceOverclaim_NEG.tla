---- MODULE RelationalAllowanceOverclaim_NEG ----
EXTENDS ALKSemanticModelWitness

OverbroadAllowedRelationSteps ==
    [obligation \in Obligations |-> Pairs(States)]

OverbroadViolatingActions ==
    [obligation \in Obligations |->
        ExpectedViolatingActionsFor(
            obligation, States, ActionLabels, Actions,
            ObligationPropertyClass,
            ObligationStates, ViolationStates,
            OverbroadAllowedRelationSteps)]

RelationalBoundaryHeld ==
    SelectedObligationBoundaryTyped(
        States, ActionLabels, Actions, Claims, Obligations, Actors,
        ObligationPropertyClass,
        ClaimObligations, ObligationStates, ViolationStates,
        OverbroadAllowedRelationSteps, OverbroadViolatingActions,
        DerivedFrom,
        LivenessActiveStates, LivenessClosedStates,
        LivenessProgressActions, LivenessOtherActions,
        LivenessWeakFairProgressActions,
        LivenessRankBound, LivenessRank,
        LivenessFairnessOwner, LivenessFairnessOwnerOf)

NegativeControlExpected == NegativeControlGate(RelationalBoundaryHeld)

====
