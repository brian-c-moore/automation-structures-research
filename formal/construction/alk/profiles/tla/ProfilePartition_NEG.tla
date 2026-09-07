---- MODULE ProfilePartition_NEG ----
EXTENDS ALKProfileConcreteInstances

MutantPartitionResult ==
    DerivedFailureCeiling(
        "partition",
        ProfileDerivedNormalGuaranteeBundle("bounded-distributed"),
        TRUE, FALSE, TRUE, TRUE, TRUE, TRUE, TRUE, TRUE)
MutantPartitionStrongGuaranteeHeld ==
    MutantPartitionResult
      \cap {"prevention", "detection", "recovery"} # {}
AdjacentPartitionLedgerHeld ==
    ProfileExactFailureLedgerHeld("bounded-distributed")

NegativeControlExpected == NegativeControlGate(MutantPartitionStrongGuaranteeHeld)

====
