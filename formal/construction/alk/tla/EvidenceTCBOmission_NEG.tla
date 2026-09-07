---- MODULE EvidenceTCBOmission_NEG ----
EXTENDS ALKEvidenceInterfaceWitness

IncompleteEvidenceClaimTCB ==
    [claim \in Claims |-> ClaimTCB[claim] \ {"audit-key"}]

EvidenceTCBClosed ==
    ClaimSpecificTCBBoundaryTyped(
        Claims, EvidenceWitnessObligations, ActionLabels, Actors,
        Dependencies, Providers,
        IncompleteEvidenceClaimTCB, GuaranteeClaimant, ALKAuthority,
        AdmittedActions, EvidenceWitnessClaimObligations, EvidenceWitnessPropertyClass,
        OwnerOf, DelegateOf, ActorDependency, ProviderDependency,
        EvidenceEvents, EvidenceWitnessForObligation,
        EvidenceProducer, CustodianOf, RetentionProviderOf,
        EvidenceWitnessFairnessOwner)

NegativeControlExpected == NegativeControlGate(EvidenceTCBClosed)

====
