---- MODULE SharedTransitionViolation_NEG ----
EXTENDS ALKConstructionTheoremWitness

ViolatingSharedSteps ==
    RegisteredSharedSteps \cup {<<"open", "bad">>}

SharedTransitionPreservationHeld ==
    SharedTransitionPremises(
        States, Components, ViolatingSharedSteps,
        ViolatingSharedSteps, AffectedComponents,
        ComponentObligationStates)

NegativeControlExpected == NegativeControlGate(SharedTransitionPreservationHeld)

====
