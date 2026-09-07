---- MODULE ProfileStaleEpoch_NEG ----
EXTENDS ALKProfileConcreteInstances

MutantStaleEpochResult ==
    DerivedFailureCeiling(
        "stale-epoch",
        ProfileDerivedNormalGuaranteeBundle("bounded-distributed"),
        TRUE, TRUE, FALSE, TRUE, TRUE, TRUE, TRUE, TRUE)
MutantStaleEpochNonLostHeld ==
    MutantStaleEpochResult # {"lost"}
AdjacentStaleEpochLedgerHeld ==
    ProfileExactFailureLedgerHeld("bounded-distributed")

NegativeControlExpected == NegativeControlGate(MutantStaleEpochNonLostHeld)

====
