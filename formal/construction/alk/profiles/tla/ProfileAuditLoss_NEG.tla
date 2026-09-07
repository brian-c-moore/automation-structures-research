---- MODULE ProfileAuditLoss_NEG ----
EXTENDS ALKProfileConcreteInstances

MutantAuditLossResult ==
    DerivedFailureCeiling(
        "audit-loss",
        ProfileDerivedNormalGuaranteeBundle("local-reference"),
        TRUE, TRUE, TRUE, TRUE, FALSE, TRUE, TRUE, TRUE)
MutantAuditDetectionRecoveryHeld ==
    MutantAuditLossResult \cap {"detection", "recovery"} # {}
AdjacentAuditLedgerHeld ==
    ProfileExactFailureLedgerHeld("local-reference")

NegativeControlExpected == NegativeControlGate(MutantAuditDetectionRecoveryHeld)

====
