---- MODULE ProfileExternalOwner_NEG ----
EXTENDS ALKProfileConcreteInstances

MutantExternalOwnerResult ==
    DerivedFailureCeiling(
        "external-owner",
        ProfileDerivedNormalGuaranteeBundle("delegated"),
        TRUE, TRUE, TRUE, TRUE, TRUE, FALSE, TRUE, TRUE)
MutantExternalOwnerPreventionHeld ==
    "prevention" \in MutantExternalOwnerResult
AdjacentExternalOwnerLedgerHeld ==
    ProfileExactFailureLedgerHeld("delegated")

NegativeControlExpected == NegativeControlGate(MutantExternalOwnerPreventionHeld)

====
