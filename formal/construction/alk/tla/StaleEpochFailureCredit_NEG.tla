---- MODULE StaleEpochFailureCredit_NEG ----
EXTENDS ALKConstructionTheoremWitness

StaleEpochFailureResultHeld ==
    FailureGuaranteeBundleMatchesDerived(
        AdvertisedUnderFailure, DerivedNormalGuaranteeBundle,
        TRUE, TRUE, FALSE, TRUE, TRUE, TRUE, TRUE, TRUE)

NegativeControlExpected == NegativeControlGate(StaleEpochFailureResultHeld)

====
