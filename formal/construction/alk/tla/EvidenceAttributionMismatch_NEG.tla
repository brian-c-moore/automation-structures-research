---- MODULE EvidenceAttributionMismatch_NEG ----
EXTENDS ALKEvidenceInterfaceWitness

MisattributedEventClaimant ==
    [event \in EvidenceEvents |-> "auditor"]

EvidenceAttributionCoherent ==
    EvidenceObligationBoundaryTyped(
        Claims, Subjects, EvidenceWitnessObligations, ActionLabels, Actors, Providers,
        EvidenceEvents, CommitActions, EvidenceForCommit,
        ClaimSubject, GuaranteeClaimant, OwnerOf,
        EvidenceWitnessClaimObligations, EvidenceWitnessPropertyClass,
        ClaimActions, EvidenceWitnessForObligation,
        EventSubject, EventAction, MisattributedEventClaimant, EventOwner,
        EventCommit, EventAssurance,
        EvidenceProducer, CustodianOf, RetentionProviderOf)

NegativeControlExpected == NegativeControlGate(EvidenceAttributionCoherent)

====
