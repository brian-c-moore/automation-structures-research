---- MODULE FalseDirectMutualClosure_NEG ----
EXTENDS ALKSemanticModelWitness

ViolatingSharedStepsForRelyEdge ==
    [edge \in Components \X Components |->
        IF edge \in DirectMutualClosureEdges
          THEN {<<"epoch-1", "failed-1">>}
        ELSE SharedStepsForRelyEdge[edge]]

DirectMutualClosureHeld ==
    RelyDischargeBoundaryTyped(
        States, Components, RelyEdges, RelyRank, RelyPropertyClassOf,
        DirectMutualClosureEdges,
        ComponentObligationStates,
        ComponentRelySteps, ComponentGuaranteeSteps,
        ViolatingSharedStepsForRelyEdge)

NegativeControlExpected == NegativeControlGate(DirectMutualClosureHeld)

====
