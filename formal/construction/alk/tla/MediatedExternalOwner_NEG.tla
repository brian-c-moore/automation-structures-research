---- MODULE MediatedExternalOwner_NEG ----
EXTENDS ALKSemanticModelWitness

MediatedExternalPathClassOf ==
    [claim \in Claims |->
        [action \in ActionLabels |->
            IF action = "external-store"
              THEN "mediated"
            ELSE PathClassOf[claim][action]]]

MediatedExternalActions ==
    [claim \in Claims |->
        MediatedActionsFor(
            claim, ClaimActions, MediatedExternalPathClassOf)]

RemainingExternalActions ==
    [claim \in Claims |->
        ExternalActionsFor(
            claim, ClaimActions, MediatedExternalPathClassOf)]

AuthorityClassificationHeld ==
    ALKAuthorityBoundaryTyped(
        Claims, ActionLabels, Actors, Dependencies,
        ClaimActions, AdmittedActions, CommitActions,
        MediatedExternalActions, RemainingExternalActions,
        MediatedExternalPathClassOf,
        OwnerOf, DelegateOf, ALKAuthority,
        ActorDependency, ClaimTCB)

NegativeControlExpected == NegativeControlGate(AuthorityClassificationHeld)

====
