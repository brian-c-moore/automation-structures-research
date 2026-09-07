---- MODULE ALKEvidenceInterfaceWitness ----
EXTENDS ALKSemanticModelWitness

\* The catalog's AuditSink clauses are safety properties. Evidence-interface
\* controls therefore need their own explicit evidence obligation; they must
\* not reclassify a catalog clause merely to make a test discriminate.
InterfaceEvidenceObligation == "witness!commit-attribution"
EvidenceWitnessObligations == Obligations \cup {InterfaceEvidenceObligation}
EvidenceWitnessClaimObligations ==
    [claim \in Claims |-> ClaimObligations[claim] \cup {InterfaceEvidenceObligation}]
EvidenceWitnessPropertyClass ==
    [obligation \in EvidenceWitnessObligations |->
        IF obligation = InterfaceEvidenceObligation THEN "evidence"
        ELSE ObligationPropertyClass[obligation]]
EvidenceWitnessForObligation ==
    [obligation \in EvidenceWitnessObligations |->
        IF obligation = InterfaceEvidenceObligation THEN EvidenceEvents
        ELSE EvidenceForObligation[obligation]]
EvidenceWitnessFairnessOwner ==
    [obligation \in EvidenceWitnessObligations |->
        IF obligation = InterfaceEvidenceObligation THEN "alk"
        ELSE LivenessFairnessOwner[obligation]]

EvidenceInterfaceBaseline ==
    /\ ModelBoundaryHolds
    /\ EvidenceEvents # {}
    /\ \A claim \in Claims : InterfaceEvidenceObligation \in EvidenceWitnessClaimObligations[claim]
    /\ EvidenceWitnessPropertyClass[InterfaceEvidenceObligation] = "evidence"
    /\ EvidenceWitnessForObligation[InterfaceEvidenceObligation] = EvidenceEvents
    /\ EvidenceObligationBoundaryTyped(
           Claims, Subjects, EvidenceWitnessObligations, ActionLabels, Actors, Providers,
           EvidenceEvents, CommitActions, EvidenceForCommit,
           ClaimSubject, GuaranteeClaimant, OwnerOf,
           EvidenceWitnessClaimObligations, EvidenceWitnessPropertyClass,
           ClaimActions, EvidenceWitnessForObligation,
           EventSubject, EventAction, EventClaimant, EventOwner,
           EventCommit, EventAssurance, EvidenceProducer, CustodianOf, RetentionProviderOf)
    /\ ClaimSpecificTCBBoundaryTyped(
           Claims, EvidenceWitnessObligations, ActionLabels, Actors, Dependencies, Providers,
           ClaimTCB, GuaranteeClaimant, ALKAuthority, AdmittedActions,
           EvidenceWitnessClaimObligations, EvidenceWitnessPropertyClass,
           OwnerOf, DelegateOf, ActorDependency, ProviderDependency,
           EvidenceEvents, EvidenceWitnessForObligation,
           EvidenceProducer, CustodianOf, RetentionProviderOf, EvidenceWitnessFairnessOwner)
====
