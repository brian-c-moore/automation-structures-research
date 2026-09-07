---- MODULE ExternalOwnerPrevention_NEG ----
EXTENDS ALKSemanticModelWitness, OwnershipAssuranceKernel

ExternalActors == {"alk", "client", "store", "auditor"}
ExternalProviders == {"auditor"}
NoExternalFailures == {}
ExternalEvidence == [state \in States |-> TRUE]

ExternalOwnerBoundary ==
    AssuranceBoundaryTyped(
        States, ExternalActors, ExternalProviders,
        "client", "store", "store", "auditor",
        "none", {}, NoExternalFailures, {},
        ExternalEvidence, TRUE, FALSE)

ExternalOwnerCeiling ==
    GuaranteeCeiling(
        "client", "store", "auditor", "none",
        {}, {}, TRUE, FALSE)

ExternalOwnerPrevention ==
    /\ ExternalOwnerBoundary
    /\ "prevention" \in ExternalOwnerCeiling

NegativeControlExpected == NegativeControlGate(ExternalOwnerPrevention)

====
