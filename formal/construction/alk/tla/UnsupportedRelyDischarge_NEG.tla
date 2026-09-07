---- MODULE UnsupportedRelyDischarge_NEG ----
EXTENDS ALKSemanticModelWitness

UnsupportedComponentGuaranteeSteps ==
    [component \in Components |->
        IF component = "admission"
          THEN {<<"epoch-1", "committed-1">>}
        ELSE ComponentGuaranteeSteps[component]]

ProviderGuaranteeDischarged ==
    RelyDischargeBoundaryTyped(
        States, Components, RelyEdges, RelyRank, RelyPropertyClassOf,
        DirectMutualClosureEdges,
        ComponentObligationStates,
        ComponentRelySteps, UnsupportedComponentGuaranteeSteps,
        SharedStepsForRelyEdge)

NegativeControlExpected == NegativeControlGate(ProviderGuaranteeDischarged)

====
