---- MODULE PostcommitPrevention_NEG ----
EXTENDS ALKSemanticModelWitness, OwnershipAssuranceKernel

AssuranceActors == {"alk", "client", "store", "auditor"}
AssuranceProviders == {"auditor"}
NoAssuranceFailures == {}
EvidenceSurvives == [state \in States |-> TRUE]

PostcommitBoundary ==
    AssuranceBoundaryTyped(
        States, AssuranceActors, AssuranceProviders,
        "client", "store", "store", "auditor",
        "postcommit", {"auditor"},
        NoAssuranceFailures, {},
        EvidenceSurvives, TRUE, FALSE)

PostcommitCeiling ==
    GuaranteeCeiling(
        "client", "store", "auditor", "postcommit",
        {"auditor"}, {}, TRUE, FALSE)

AdvertisedPrevention ==
    /\ PostcommitBoundary
    /\ "detection" \in PostcommitCeiling
    /\ "prevention" \in PostcommitCeiling

NegativeControlExpected == NegativeControlGate(AdvertisedPrevention)

====
