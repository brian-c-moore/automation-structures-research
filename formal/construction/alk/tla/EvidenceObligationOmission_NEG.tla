---- MODULE EvidenceObligationOmission_NEG ----
EXTENDS ALKEvidenceInterfaceWitness

MissingEvidenceForObligation ==
    [obligation \in EvidenceWitnessObligations |-> {}]

EvidenceObligationAttributionHeld ==
    EvidenceObligationBoundaryTyped(
        Claims, Subjects, EvidenceWitnessObligations, ActionLabels, Actors, Providers,
        EvidenceEvents, CommitActions, EvidenceForCommit,
        ClaimSubject, GuaranteeClaimant, OwnerOf,
        EvidenceWitnessClaimObligations, EvidenceWitnessPropertyClass,
        ClaimActions, MissingEvidenceForObligation,
        EventSubject, EventAction, EventClaimant, EventOwner,
        EventCommit, EventAssurance,
        EvidenceProducer, CustodianOf, RetentionProviderOf)

NegativeControlExpected == NegativeControlGate(EvidenceObligationAttributionHeld)

====
