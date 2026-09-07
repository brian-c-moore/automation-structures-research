---- MODULE PartitionFailureCredit_NEG ----
EXTENDS ALKConstructionTheoremWitness

PartitionFailureMutationHeld ==
    FailureGuaranteeBundleMatchesDerived(
        AdvertisedUnderFailure, DerivedNormalGuaranteeBundle,
        TRUE, FALSE, TRUE, TRUE, TRUE, TRUE, TRUE, TRUE)

RetryExhaustionMutationHeld ==
    FailureGuaranteeBundleMatchesDerived(
        AdvertisedUnderFailure, DerivedNormalGuaranteeBundle,
        TRUE, TRUE, TRUE, TRUE, TRUE, TRUE, FALSE, TRUE)

PartitionFailureResultHeld ==
    PartitionFailureMutationHeld \/ RetryExhaustionMutationHeld

NegativeControlExpected == NegativeControlGate(PartitionFailureResultHeld)

====
