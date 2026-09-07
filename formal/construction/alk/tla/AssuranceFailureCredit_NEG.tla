---- MODULE AssuranceFailureCredit_NEG ----
EXTENDS ALKConstructionTheoremWitness

AssuranceFailureResultHeld ==
    FailureGuaranteeBundleMatchesDerived(
        AdvertisedUnderFailure, DerivedNormalGuaranteeBundle,
        TRUE, TRUE, TRUE, FALSE, TRUE, TRUE, TRUE, TRUE)

NegativeControlExpected == NegativeControlGate(AssuranceFailureResultHeld)

====
