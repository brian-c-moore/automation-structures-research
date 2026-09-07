---- MODULE IndependentGuaranteeAdvertisement_NEG ----
EXTENDS ALKConstructionTheoremWitness

ExternalCommitOwner ==
    [action \in ActionLabels |->
        IF action = "commit" THEN "custodian" ELSE OwnerOf[action]]
PostcommitAssurance ==
    [action \in ActionLabels |->
        IF action = "commit" THEN "postcommit" ELSE AssurancePositionOf[action]]

DerivedGuaranteeBundleHeld ==
    ClaimGuaranteeBundleMatchesDerived(
        Claims, AdvertisedGuaranteeBundle,
        RegisteredGuarantees, GuaranteeKindOf,
        ClaimCommitActions, GuaranteeClaimant, ExternalCommitOwner,
        AssuranceProviderOf, PostcommitAssurance,
        PreventionControllers, UnavailableProviders,
        PersistentEvidenceFor, RecoveryAvailableFor)

NegativeControlExpected == NegativeControlGate(DerivedGuaranteeBundleHeld)

====
