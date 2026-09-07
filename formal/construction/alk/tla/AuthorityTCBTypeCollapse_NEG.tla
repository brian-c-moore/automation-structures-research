---- MODULE AuthorityTCBTypeCollapse_NEG ----
EXTENDS ALKSemanticModelWitness

CollapsedDependencies == Actors
CollapsedActorDependency == [actor \in Actors |-> actor]
CollapsedClaimTCB == [claim \in Claims |-> Actors]

AuthorityTCBDistinct ==
    ALKAuthorityBoundaryTyped(
        Claims, ActionLabels, Actors, CollapsedDependencies,
        ClaimActions, AdmittedActions,
        CommitActions, MediatedActions, ExternalActions,
        PathClassOf,
        OwnerOf, DelegateOf, ALKAuthority,
        CollapsedActorDependency, CollapsedClaimTCB)

NegativeControlExpected == NegativeControlGate(AuthorityTCBDistinct)

====
