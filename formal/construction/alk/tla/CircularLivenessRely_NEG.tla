---- MODULE CircularLivenessRely_NEG ----
EXTENDS ALKSemanticModelWitness

CircularLivenessRelyPropertyClassOf ==
    [edge \in RelyEdges |->
        IF edge \in DirectMutualClosureEdges
          THEN "liveness"
        ELSE RelyPropertyClassOf[edge]]

CircularLivenessRelyRejected ==
    RelyDischargeBoundaryTyped(
        States, Components, RelyEdges, RelyRank,
        CircularLivenessRelyPropertyClassOf,
        DirectMutualClosureEdges,
        ComponentObligationStates,
        ComponentRelySteps, ComponentGuaranteeSteps,
        SharedStepsForRelyEdge)

NegativeControlExpected == NegativeControlGate(CircularLivenessRelyRejected)

====
