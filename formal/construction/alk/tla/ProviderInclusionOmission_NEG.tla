---- MODULE ProviderInclusionOmission_NEG ----
EXTENDS ALKConstructionTheoremWitness

UnsupportedProviderGuaranteeSteps ==
    [component \in Components |->
        IF component = "component-b"
          THEN {<<"open", "open">>}
          ELSE ComponentGuaranteeSteps[component]]

ProviderGuaranteeInclusionHeld ==
    ProviderBackedRelyPremises(
        States, Components, RelyEdges, RelyRank, RelyPropertyClassOf,
        DirectMutualClosureEdges,
        ComponentObligationStates,
        ComponentRelySteps, UnsupportedProviderGuaranteeSteps,
        SharedStepsForRelyEdge, RegisteredSharedSteps)

NegativeControlExpected == NegativeControlGate(ProviderGuaranteeInclusionHeld)

====
