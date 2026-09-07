---- MODULE AuditFailureCredit_NEG ----
EXTENDS ALKConstructionTheoremWitness

AuditLossMutationHeld ==
    FailureGuaranteeBundleMatchesDerived(
        AdvertisedUnderFailure, DerivedNormalGuaranteeBundle,
        TRUE, TRUE, TRUE, TRUE, FALSE, TRUE, TRUE, TRUE)

RecoverySensitiveNormalBundle ==
    DerivedNormalGuaranteeBundle \cup {"recovery"}
RecoverySensitiveAdvertisedUnderFailure ==
    DerivedFailureGuaranteeBundle(
        RecoverySensitiveNormalBundle,
        TRUE, TRUE, TRUE, TRUE, TRUE, TRUE, TRUE, TRUE)

RecoveryFailureAdjacentBoundaryHeld ==
    FailureGuaranteeBundleMatchesDerived(
        RecoverySensitiveAdvertisedUnderFailure,
        RecoverySensitiveNormalBundle,
        TRUE, TRUE, TRUE, TRUE, TRUE, TRUE, TRUE, TRUE)

RecoveryFailureMutationHeld ==
    FailureGuaranteeBundleMatchesDerived(
        RecoverySensitiveAdvertisedUnderFailure,
        RecoverySensitiveNormalBundle,
        TRUE, TRUE, TRUE, TRUE, TRUE, TRUE, TRUE, FALSE)

AuditFailureResultHeld ==
    AuditLossMutationHeld \/ RecoveryFailureMutationHeld

NegativeControlExpected == NegativeControlGate(AuditFailureResultHeld)

====
