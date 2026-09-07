---- MODULE ProfileCircularRely_NEG ----
EXTENDS ALKProfileConcreteInstances

MutantSharedSteps == {<<"open", "failed">>}
MutantSharedStepsForRelyEdge ==
    [edge \in ProfileComponents \X ProfileComponents |-> MutantSharedSteps]
MutantCircularRelyHeld ==
    ProviderBackedRelyPremises(
        ProfileStates, ProfileComponents, ProfileRelyEdges("modular"),
        ProfileRelyRank("modular"),
        ProfileRelyPropertyClassOf("modular"),
        ProfileDirectMutualClosureEdges("modular"),
        ProfileComponentObligationStates,
        ProfileComponentRelySteps("modular"),
        ProfileComponentGuaranteeSteps("modular"),
        MutantSharedStepsForRelyEdge, MutantSharedSteps)
AdjacentModularSharedTransitionHeld ==
    ProfileSharedTransitionPremisesHeld("modular")

NegativeControlExpected == NegativeControlGate(MutantCircularRelyHeld)

====
