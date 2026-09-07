---- MODULE LivenessRankFairnessOmission_NEG ----
EXTENDS ALKConstructionTheoremWitness

TemporalObligation == "PropagationPass!EventualSettledOrIterationLimit"
TemporalClaimObligations == [claim \in Claims |-> {TemporalObligation}]
TemporalSelectedFamilies == SelectedFamilies \cup {"progress"}
TemporalFormalClosedStates == LivenessClosedStates[TemporalObligation]
TemporalFormalProgressSteps ==
    ActionUnion(LivenessProgressActions[TemporalObligation], PotentialActions)
TemporalFormalOtherSteps ==
    ActionUnion(LivenessOtherActions[TemporalObligation], PotentialActions)
TemporalFormalRankBound == LivenessRankBound[TemporalObligation]
TemporalFormalRank == LivenessRank[TemporalObligation]
TemporalFormalFairnessOwner == LivenessFairnessOwner[TemporalObligation]
TemporalFormalFairnessOwnerOf ==
    [step \in TemporalFormalProgressSteps |-> TemporalFormalFairnessOwner]
MissingWeakFairProgressActions ==
    [obligation \in Obligations |->
        IF obligation = TemporalObligation
          THEN {}
          ELSE LivenessWeakFairProgressActions[obligation]]
FlatTemporalRank ==
    [obligation \in Obligations |->
        IF obligation = TemporalObligation
          THEN [state \in States |-> 0]
          ELSE LivenessRank[obligation]]
MismatchedFormalRank == [state \in States |-> 0]

TemporalLivenessBoundaryHeld ==
    SelectedObligationBoundaryTyped(
        States, ActionLabels, PotentialActions,
        Claims, Obligations, Actors,
        ObligationPropertyClass,
        TemporalClaimObligations, ObligationStates, ViolationStates,
        AllowedRelationSteps, ViolatingActions, DerivedFrom,
        LivenessActiveStates, LivenessClosedStates,
        LivenessProgressActions, LivenessOtherActions,
        LivenessWeakFairProgressActions,
        LivenessRankBound, LivenessRank,
        LivenessFairnessOwner, LivenessFairnessOwnerOf)

TemporalLivenessKernelBindingHeld ==
    ExactLivenessKernelBinding(
        Claims, Obligations, ActionLabels, PotentialActions, Actors,
        TemporalClaimObligations, ObligationPropertyClass,
        LivenessClosedStates, LivenessProgressActions,
        LivenessOtherActions, LivenessRankBound, LivenessRank,
        LivenessFairnessOwner, LivenessFairnessOwnerOf,
        TemporalSelectedFamilies,
        TemporalFormalClosedStates, TemporalFormalProgressSteps,
        TemporalFormalOtherSteps, TemporalFormalRankBound,
        TemporalFormalRank, TemporalFormalFairnessOwner,
        TemporalFormalFairnessOwnerOf)

MissingWeakFairRegistrationHeld ==
    SelectedObligationBoundaryTyped(
        States, ActionLabels, PotentialActions,
        Claims, Obligations, Actors,
        ObligationPropertyClass,
        TemporalClaimObligations, ObligationStates, ViolationStates,
        AllowedRelationSteps, ViolatingActions, DerivedFrom,
        LivenessActiveStates, LivenessClosedStates,
        LivenessProgressActions, LivenessOtherActions,
        MissingWeakFairProgressActions,
        LivenessRankBound, LivenessRank,
        LivenessFairnessOwner, LivenessFairnessOwnerOf)

StrictRankPremiseHeld ==
    SelectedObligationBoundaryTyped(
        States, ActionLabels, PotentialActions,
        Claims, Obligations, Actors,
        ObligationPropertyClass,
        TemporalClaimObligations, ObligationStates, ViolationStates,
        AllowedRelationSteps, ViolatingActions, DerivedFrom,
        LivenessActiveStates, LivenessClosedStates,
        LivenessProgressActions, LivenessOtherActions,
        LivenessWeakFairProgressActions,
        LivenessRankBound, FlatTemporalRank,
        LivenessFairnessOwner, LivenessFairnessOwnerOf)

MismatchedKernelRankBindingHeld ==
    ExactLivenessKernelBinding(
        Claims, Obligations, ActionLabels, PotentialActions, Actors,
        TemporalClaimObligations, ObligationPropertyClass,
        LivenessClosedStates, LivenessProgressActions,
        LivenessOtherActions, LivenessRankBound, LivenessRank,
        LivenessFairnessOwner, LivenessFairnessOwnerOf,
        TemporalSelectedFamilies,
        TemporalFormalClosedStates, TemporalFormalProgressSteps,
        TemporalFormalOtherSteps, TemporalFormalRankBound,
        MismatchedFormalRank, TemporalFormalFairnessOwner,
        TemporalFormalFairnessOwnerOf)

ExactLivenessPremisesHeld ==
    MissingWeakFairRegistrationHeld
      \/ StrictRankPremiseHeld
      \/ MismatchedKernelRankBindingHeld

NegativeControlExpected == NegativeControlGate(ExactLivenessPremisesHeld)

====
