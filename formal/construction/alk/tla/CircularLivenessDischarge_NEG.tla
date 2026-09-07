---- MODULE CircularLivenessDischarge_NEG ----
EXTENDS ALKConstructionTheoremWitness

CircularRelyEdges ==
    {<<"component-a", "component-b">>,
     <<"component-b", "component-a">>}
CircularRelyRank == [component \in Components |-> 0]
CircularRelyPropertyClassOf ==
    [edge \in CircularRelyEdges |-> "liveness"]
CircularSafetyPropertyClassOf ==
    [edge \in CircularRelyEdges |-> "safety"]
CircularDirectMutualClosureEdges == CircularRelyEdges
CircularComponentRelySteps ==
    [component \in Components |->
        IF component = "component-a"
          THEN ComponentGuaranteeSteps["component-b"]
          ELSE ComponentGuaranteeSteps["component-a"]]
CircularSharedStepsForRelyEdge ==
    [edge \in Components \X Components |-> RegisteredSharedSteps]
ShadowCircularSharedStepsForRelyEdge ==
    [edge \in Components \X Components |-> {<<"closed", "closed">>}]

CircularLivenessClassCreditHeld ==
    ProviderBackedRelyPremises(
        States, Components, CircularRelyEdges,
        CircularRelyRank, CircularRelyPropertyClassOf,
        CircularDirectMutualClosureEdges,
        ComponentObligationStates,
        CircularComponentRelySteps, ComponentGuaranteeSteps,
        CircularSharedStepsForRelyEdge, RegisteredSharedSteps)

CircularSafetyAdjacentBoundaryHeld ==
    ProviderBackedRelyPremises(
        States, Components, CircularRelyEdges,
        CircularRelyRank, CircularSafetyPropertyClassOf,
        CircularDirectMutualClosureEdges,
        ComponentObligationStates,
        CircularComponentRelySteps, ComponentGuaranteeSteps,
        CircularSharedStepsForRelyEdge, RegisteredSharedSteps)

ShadowDirectMutualSharedRelationHeld ==
    ProviderBackedRelyPremises(
        States, Components, CircularRelyEdges,
        CircularRelyRank, CircularSafetyPropertyClassOf,
        CircularDirectMutualClosureEdges,
        ComponentObligationStates,
        CircularComponentRelySteps, ComponentGuaranteeSteps,
        ShadowCircularSharedStepsForRelyEdge, RegisteredSharedSteps)

CircularLivenessDischargeHeld ==
    CircularLivenessClassCreditHeld
      \/ ShadowDirectMutualSharedRelationHeld

NegativeControlExpected == NegativeControlGate(CircularLivenessDischargeHeld)

====
