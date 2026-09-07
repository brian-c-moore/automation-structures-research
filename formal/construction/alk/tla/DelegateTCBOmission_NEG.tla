---- MODULE DelegateTCBOmission_NEG ----
EXTENDS ALKSemanticModelWitness

IncompleteClaimTCB ==
    [claim \in Claims |-> ClaimTCB[claim] \ {"store-service"}]

DelegateTCBClosed ==
    ALKAuthorityBoundaryTyped(
        Claims, ActionLabels, Actors, Dependencies,
        ClaimActions, AdmittedActions,
        CommitActions, MediatedActions, ExternalActions,
        PathClassOf,
        OwnerOf, DelegateOf, ALKAuthority,
        ActorDependency, IncompleteClaimTCB)

NegativeControlExpected == NegativeControlGate(DelegateTCBClosed)

====
