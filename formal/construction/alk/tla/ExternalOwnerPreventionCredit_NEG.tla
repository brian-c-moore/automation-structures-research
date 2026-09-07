---- MODULE ExternalOwnerPreventionCredit_NEG ----
EXTENDS ALKConstructionTheoremWitness

ExternalCommitOwner ==
    [action \in ActionLabels |->
        IF action = "commit" THEN "custodian" ELSE OwnerOf[action]]

ExternalPreventionControllers == {}

ExternalOwnerInventoryHeld ==
    CommitAssuranceInventoryTyped(
        Claims, ActionLabels, Actors, Providers,
        ClaimCommitActions, GuaranteeClaimant, ExternalCommitOwner,
        AssuranceProviderOf, AssurancePositionOf,
        ExternalPreventionControllers, UnavailableProviders,
        PersistentEvidenceFor, RecoveryAvailableFor)

ExternalEventOwner ==
    [event \in EvidenceEvents |-> "custodian"]

ExternalOwnerCommitEvidenceHeld ==
    OwnedCommitEvidencePremises(
        States, KernelCheckActMode,
        KernelCheckResultStates, KernelPredicateStates,
        KernelInterferenceSteps, GovernedCommitSteps,
        Claims, Subjects, ActionLabels, Actors, Providers,
        EvidenceEvents, ClaimCommitActions, EvidenceRequiredActions,
        EvidenceForCommit, ClaimSubject, GuaranteeClaimant,
        ExternalCommitOwner, AssurancePositionOf,
        EventSubject, EventAction, EventClaimant, ExternalEventOwner,
        EventCommit, EventAssurance,
        EvidenceProducer, CustodianOf, RetentionProviderOf)

ExternalOwnerCommitCeiling ==
    CommitGuaranteeCeiling(
        "bounded-claim", "commit",
        GuaranteeClaimant, ExternalCommitOwner,
        AssuranceProviderOf, AssurancePositionOf,
        ExternalPreventionControllers, UnavailableProviders,
        PersistentEvidenceFor, RecoveryAvailableFor)

ExternalOwnerPreventionCreditHeld ==
    /\ ExternalOwnerInventoryHeld
    /\ ExternalOwnerCommitEvidenceHeld
    /\ "prevention" \in ExternalOwnerCommitCeiling

NegativeControlExpected == NegativeControlGate(ExternalOwnerPreventionCreditHeld)

====
