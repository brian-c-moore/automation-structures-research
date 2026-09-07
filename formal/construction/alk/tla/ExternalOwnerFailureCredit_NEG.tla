---- MODULE ExternalOwnerFailureCredit_NEG ----
EXTENDS ALKConstructionTheoremWitness

ExternalOwnerFailureResultHeld ==
    FailureGuaranteeBundleMatchesDerived(
        AdvertisedUnderFailure, DerivedNormalGuaranteeBundle,
        TRUE, TRUE, TRUE, TRUE, TRUE, FALSE, TRUE, TRUE)

NegativeControlExpected == NegativeControlGate(ExternalOwnerFailureResultHeld)

====
