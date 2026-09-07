---- MODULE ClaimRelativeOwnership ----
EXTENDS Naturals

PropertyForms == {"safety", "liveness", "evidence", "relational"}

ClaimFrameType(
        Subjects, Obligations, Modes, Scopes,
        ObservationBoundaries, AuthorityBoundaries,
        Claimants, FailureModels, Abstractions, LifecyclePhases) ==
    [subject : Subjects,
     obligation : Obligations,
     mode : Modes,
     scope : Scopes,
     observationBoundary : ObservationBoundaries,
     authorityBoundary : AuthorityBoundaries,
     claimant : Claimants,
     failureModel : FailureModels,
     abstraction : Abstractions,
     lifecyclePhase : LifecyclePhases,
     propertyForm : PropertyForms]

ClaimFramesTyped(
        Frames, Subjects, Obligations, Modes, Scopes,
        ObservationBoundaries, AuthorityBoundaries,
        Claimants, FailureModels, Abstractions, LifecyclePhases) ==
    /\ Frames # {}
    /\ Frames \subseteq ClaimFrameType(
           Subjects, Obligations, Modes, Scopes,
           ObservationBoundaries, AuthorityBoundaries,
           Claimants, FailureModels, Abstractions, LifecyclePhases)

FrameRelationTyped(Frames, Relation) ==
    /\ Relation \subseteq (Frames \X Frames)
    /\ \A frame \in Frames : <<frame, frame>> \notin Relation

AbstractionRelationsTyped(Frames, RefinesTo, ComposesInto) ==
    /\ FrameRelationTyped(Frames, RefinesTo)
    /\ FrameRelationTyped(Frames, ComposesInto)

AuthorityBindingsTyped(
        Frames, Principals, Behaviors,
        DecisiveOf, ControlsOf, ExcludesOf) ==
    /\ Principals # {}
    /\ Behaviors # {}
    /\ DecisiveOf \in [Frames -> SUBSET Behaviors]
    /\ ControlsOf \in [Frames -> [Principals -> SUBSET Behaviors]]
    /\ ExcludesOf \in [Frames -> [Principals -> SUBSET Behaviors]]
    /\ \A frame \in Frames : DecisiveOf[frame] # {}

Covers(
        frame, principal, DecisiveOf, ControlsOf, ExcludesOf) ==
    DecisiveOf[frame]
        \subseteq ControlsOf[frame][principal] \cup ExcludesOf[frame][principal]

EligibleOwners(
        frame, Principals, DecisiveOf, ControlsOf, ExcludesOf) ==
    {principal \in Principals :
        Covers(frame, principal, DecisiveOf, ControlsOf, ExcludesOf)}

OwnersOf(frame, Principals, Ownership) ==
    {principal \in Principals : <<frame, principal>> \in Ownership}

OwnedFrames(Frames, Principals, Ownership) ==
    {frame \in Frames : OwnersOf(frame, Principals, Ownership) # {}}

UnownedFrames(Frames, Principals, Ownership) ==
    Frames \ OwnedFrames(Frames, Principals, Ownership)

CanonicalOwner(frame, Principals, Ownership) ==
    CHOOSE principal \in Principals : <<frame, principal>> \in Ownership

SingleOwnerPerFrame(Frames, Principals, Ownership) ==
    \A frame \in Frames :
      \A first \in Principals :
        \A second \in Principals :
          <<frame, first>> \in Ownership
            /\ <<frame, second>> \in Ownership
            => first = second

CanonicalOwnershipTyped(
        Frames, Principals, Ownership,
        DecisiveOf, ControlsOf, ExcludesOf) ==
    /\ Ownership \subseteq (Frames \X Principals)
    /\ SingleOwnerPerFrame(Frames, Principals, Ownership)
    /\ \A pair \in Ownership :
          Covers(
              pair[1], pair[2],
              DecisiveOf, ControlsOf, ExcludesOf)

CompleteOwnershipDisposition(
        Frames, Principals, Ownership,
        DecisiveOf, ControlsOf, ExcludesOf) ==
    /\ CanonicalOwnershipTyped(
           Frames, Principals, Ownership,
           DecisiveOf, ControlsOf, ExcludesOf)
    /\ OwnedFrames(Frames, Principals, Ownership)
         \cup UnownedFrames(Frames, Principals, Ownership) = Frames
    /\ OwnedFrames(Frames, Principals, Ownership)
         \cap UnownedFrames(Frames, Principals, Ownership) = {}

TechnicalAccountabilityTyped(
        Frames, Principals, Ownership, Accountability) ==
    /\ Accountability \subseteq (Frames \X Principals)
    /\ Accountability = Ownership

DependencyBoundariesTyped(
        Frames, Principals, Mechanisms, Ownership,
        MechanismController, AuthorityBaseOf,
        ClaimTCBOf, ExternalReliesOf) ==
    /\ Mechanisms # {}
    /\ MechanismController \in [Mechanisms -> Principals]
    /\ AuthorityBaseOf \in [Frames -> SUBSET Mechanisms]
    /\ ClaimTCBOf \in [Frames -> SUBSET Mechanisms]
    /\ ExternalReliesOf \in [Frames -> SUBSET Mechanisms]
    /\ \A frame \in Frames :
          /\ AuthorityBaseOf[frame] \subseteq ClaimTCBOf[frame]
          /\ ExternalReliesOf[frame]
               = ClaimTCBOf[frame] \ AuthorityBaseOf[frame]
    /\ \A frame \in OwnedFrames(Frames, Principals, Ownership) :
          \A mechanism \in AuthorityBaseOf[frame] :
            MechanismController[mechanism]
              = CanonicalOwner(frame, Principals, Ownership)
    /\ \A frame \in UnownedFrames(Frames, Principals, Ownership) :
          AuthorityBaseOf[frame] = {}

GuaranteeRecordsTyped(
        Frames, Principals, EvidenceItems, Mechanisms,
        Assumptions, Ceilings, Guarantees, Ownership,
        ClaimTCBOf, GuaranteeFrame, GuaranteeIssuer,
        GuaranteeRecipient, GuaranteeEvidence,
        GuaranteeRelies, GuaranteeTCB, GuaranteeCeiling) ==
    /\ GuaranteeFrame \in
         [Guarantees -> OwnedFrames(Frames, Principals, Ownership)]
    /\ GuaranteeIssuer \in [Guarantees -> Principals]
    /\ GuaranteeRecipient \in [Guarantees -> Principals]
    /\ GuaranteeEvidence \in [Guarantees -> SUBSET EvidenceItems]
    /\ GuaranteeRelies \in [Guarantees -> SUBSET Assumptions]
    /\ GuaranteeTCB \in [Guarantees -> SUBSET Mechanisms]
    /\ GuaranteeCeiling \in [Guarantees -> Ceilings]
    /\ \A guarantee \in Guarantees :
          /\ GuaranteeIssuer[guarantee]
               = CanonicalOwner(
                    GuaranteeFrame[guarantee], Principals, Ownership)
          /\ GuaranteeRecipient[guarantee]
               = GuaranteeFrame[guarantee].claimant
          /\ GuaranteeTCB[guarantee]
               = ClaimTCBOf[GuaranteeFrame[guarantee]]

AssuranceRecordsTyped(
        Frames, Principals, Propositions, EvidenceItems,
        ObservationTimes, IndependenceClasses, Limits,
        Assurances, AssuranceFrame, AssuranceClaimant,
        AssuranceSource, AssuranceProposition,
        AssuranceEvidence, AssuranceObservation,
        AssuranceIndependence, AssuranceLimits) ==
    /\ AssuranceFrame \in [Assurances -> Frames]
    /\ AssuranceClaimant \in [Assurances -> Principals]
    /\ AssuranceSource \in [Assurances -> Principals]
    /\ AssuranceProposition \in [Assurances -> Propositions]
    /\ AssuranceEvidence \in [Assurances -> SUBSET EvidenceItems]
    /\ AssuranceObservation \in [Assurances -> ObservationTimes]
    /\ AssuranceIndependence \in [Assurances -> IndependenceClasses]
    /\ AssuranceLimits \in [Assurances -> SUBSET Limits]
    /\ \A assurance \in Assurances :
          AssuranceClaimant[assurance]
            = AssuranceFrame[assurance].claimant

DelegationKinds == {"work", "authority"}

DelegationRecordsTyped(
        Frames, Principals, Behaviors, Delegations,
        DelegationFrame, Delegator, Delegate,
        DelegationKind, DelegatedBehaviors) ==
    /\ DelegationFrame \in [Delegations -> Frames]
    /\ Delegator \in [Delegations -> Principals]
    /\ Delegate \in [Delegations -> Principals]
    /\ DelegationKind \in [Delegations -> DelegationKinds]
    /\ DelegatedBehaviors \in [Delegations -> SUBSET Behaviors]
    /\ \A delegation \in Delegations :
          /\ Delegator[delegation] # Delegate[delegation]
          /\ DelegatedBehaviors[delegation] # {}

OwnershipPreservingDelegation(
        delegation, Frames, Principals, Ownership,
        DelegationFrame, Delegator, DelegationKind,
        DecisiveOf, ControlsOf, ExcludesOf) ==
    LET frame == DelegationFrame[delegation]
        owner == CanonicalOwner(frame, Principals, Ownership)
    IN
    /\ frame \in OwnedFrames(Frames, Principals, Ownership)
    /\ DelegationKind[delegation] = "work"
    /\ owner = Delegator[delegation]
    /\ Covers(frame, owner, DecisiveOf, ControlsOf, ExcludesOf)

OwnershipTransferResult(
        delegation, Frames, Principals, Ownership, Accountability,
        DelegationFrame, Delegator, Delegate, DelegationKind,
        DecisiveOf, ControlsOf, ExcludesOf) ==
    LET frame == DelegationFrame[delegation]
        former == Delegator[delegation]
        recipient == Delegate[delegation]
    IN
    /\ frame \in OwnedFrames(Frames, Principals, Ownership)
    /\ DelegationKind[delegation] = "authority"
    /\ CanonicalOwner(frame, Principals, Ownership) = recipient
    /\ Covers(frame, recipient, DecisiveOf, ControlsOf, ExcludesOf)
    /\ ~Covers(frame, former, DecisiveOf, ControlsOf, ExcludesOf)
    /\ <<frame, recipient>> \in Accountability

ClaimRecordSeparation(
        Frames, Principals, Guarantees, Ownership,
        GuaranteeFrame, GuaranteeIssuer,
        Assurances, AssuranceFrame, AssuranceClaimant) ==
    \A assurance \in Assurances :
      LET frame == AssuranceFrame[assurance]
          claimant == AssuranceClaimant[assurance]
      IN
      frame \in OwnedFrames(Frames, Principals, Ownership)
        /\ claimant # CanonicalOwner(frame, Principals, Ownership)
        => \A guarantee \in Guarantees :
             GuaranteeFrame[guarantee] = frame
               => GuaranteeIssuer[guarantee] # claimant

====
