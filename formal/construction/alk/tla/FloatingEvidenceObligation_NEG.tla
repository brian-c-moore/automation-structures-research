---- MODULE FloatingEvidenceObligation_NEG ----
EXTENDS ALKEvidenceInterfaceWitness

FloatingEvidenceEvents == EvidenceEvents \cup {"floating-event"}
FloatingEvidenceForObligation ==
    [obligation \in EvidenceWitnessObligations |->
        IF EvidenceWitnessPropertyClass[obligation] = "evidence"
          THEN {"floating-event"}
        ELSE {}]
FloatingEventSubject ==
    [event \in FloatingEvidenceEvents |->
        IF event = "floating-event" THEN "job" ELSE EventSubject[event]]
FloatingEventAction ==
    [event \in FloatingEvidenceEvents |->
        IF event = "floating-event" THEN "commit" ELSE EventAction[event]]
FloatingEventOwner ==
    [event \in FloatingEvidenceEvents |->
        IF event = "floating-event" THEN "alk" ELSE EventOwner[event]]
FloatingEventClaimant ==
    [event \in FloatingEvidenceEvents |->
        IF event = "floating-event" THEN "client" ELSE EventClaimant[event]]
FloatingEventCommit ==
    [event \in FloatingEvidenceEvents |->
        IF event = "floating-event" THEN "commit" ELSE EventCommit[event]]
FloatingEventAssurance ==
    [event \in FloatingEvidenceEvents |->
        IF event = "floating-event" THEN "at-commit" ELSE EventAssurance[event]]
FloatingEvidenceProducer ==
    [event \in FloatingEvidenceEvents |->
        IF event = "floating-event" THEN "alk" ELSE EvidenceProducer[event]]
FloatingCustodianOf ==
    [event \in FloatingEvidenceEvents |->
        IF event = "floating-event" THEN "auditor" ELSE CustodianOf[event]]
FloatingRetentionProviderOf ==
    [event \in FloatingEvidenceEvents |->
        IF event = "floating-event"
          THEN "local-log"
        ELSE RetentionProviderOf[event]]

EvidenceObligationCommitBound ==
    EvidenceObligationBoundaryTyped(
        Claims, Subjects, EvidenceWitnessObligations, ActionLabels, Actors, Providers,
        FloatingEvidenceEvents, CommitActions, EvidenceForCommit,
        ClaimSubject, GuaranteeClaimant, OwnerOf,
        EvidenceWitnessClaimObligations, EvidenceWitnessPropertyClass,
        ClaimActions, FloatingEvidenceForObligation,
        FloatingEventSubject, FloatingEventAction,
        FloatingEventClaimant, FloatingEventOwner,
        FloatingEventCommit, FloatingEventAssurance,
        FloatingEvidenceProducer, FloatingCustodianOf,
        FloatingRetentionProviderOf)

NegativeControlExpected == NegativeControlGate(EvidenceObligationCommitBound)

====
