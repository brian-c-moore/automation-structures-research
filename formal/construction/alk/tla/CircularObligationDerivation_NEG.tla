---- MODULE CircularObligationDerivation_NEG ----
EXTENDS ALKSemanticModelWitness

LeftObligation == "Budget!SafetyInvariant"
RightObligation == "ResourceRegistry!UniqueMapping"

CyclicDerivedFrom ==
    [obligation \in Obligations |->
        CASE obligation = LeftObligation -> {RightObligation}
          [] obligation = RightObligation -> {LeftObligation}
          [] OTHER -> DerivedFrom[obligation]]

SelectedObligationBoundaryHeld ==
    SelectedObligationBoundaryTyped(
        States, ActionLabels, Actions, Claims, Obligations, Actors,
        ObligationPropertyClass,
        ClaimObligations, ObligationStates, ViolationStates,
        AllowedRelationSteps, ViolatingActions,
        CyclicDerivedFrom,
        LivenessActiveStates, LivenessClosedStates,
        LivenessProgressActions, LivenessOtherActions,
        LivenessWeakFairProgressActions,
        LivenessRankBound, LivenessRank,
        LivenessFairnessOwner, LivenessFairnessOwnerOf)

NegativeControlExpected == NegativeControlGate(SelectedObligationBoundaryHeld)

====
