---- MODULE ALKProfiles_Proof ----
EXTENDS ALKProfiles, TLAPS

ProfileNormalBundle ==
    {"prevention", "detection", "recovery", "conditional"}

ProfileScenarioLedger ==
    [failureClass \in ALKFailureClasses |->
        ProfileFailureScenarioCeiling(
            failureClass, ProfileNormalBundle)]

THEOREM EveryNamedFailureHasTheExactRegisteredCeiling ==
    ExactProfileFailureLedger(ProfileNormalBundle, ProfileScenarioLedger)
BY SMT DEF ProfileNormalBundle, ProfileScenarioLedger,
           ExactProfileFailureLedger,
           ProfileFailureScenarioCeiling,
           ExpectedProfileFailureCeiling,
           DerivedFailureCeiling, ALKFailureClasses,
           GuaranteeKinds

THEOREM DelegatedVariantsRespectAssurancePositionAndAvailability ==
    DelegatedVariantCeilingsExact
BY SMT DEF DelegatedVariantCeilingsExact,
           DelegatedPrecommitCeiling,
           DelegatedPostcommitCeiling,
           DelegatedUnavailableCeiling,
           GuaranteeCeiling, PreventionSupported,
           DetectionSupported, RecoverySupported,
           AssuranceHealthy, GuaranteeKinds

====
