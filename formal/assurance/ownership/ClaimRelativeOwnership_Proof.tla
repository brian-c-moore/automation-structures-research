---- MODULE ClaimRelativeOwnership_Proof ----
EXTENDS ClaimRelativeOwnership, TLAPS

CONSTANTS Frames, Principals, Behaviors,
          DecisiveOf, ControlsOf, ExcludesOf,
          Ownership, Accountability,
          EvidenceItems, Mechanisms, Assumptions, Ceilings,
          Guarantees, ClaimTCBOf,
          GuaranteeFrame, GuaranteeIssuer, GuaranteeRecipient,
          GuaranteeEvidence, GuaranteeRelies, GuaranteeTCB,
          GuaranteeCeiling,
          MechanismController, AuthorityBaseOf, ExternalReliesOf,
          Assurances, AssuranceFrame, AssuranceClaimant

ASSUME AuthorityBindingsHeld ==
    AuthorityBindingsTyped(
        Frames, Principals, Behaviors,
        DecisiveOf, ControlsOf, ExcludesOf)

ASSUME CompleteOwnershipHeld ==
    CompleteOwnershipDisposition(
        Frames, Principals, Ownership,
        DecisiveOf, ControlsOf, ExcludesOf)

ASSUME TechnicalAccountabilityHeld ==
    TechnicalAccountabilityTyped(
        Frames, Principals, Ownership, Accountability)

ASSUME DependencyBoundariesHeld ==
    DependencyBoundariesTyped(
        Frames, Principals, Mechanisms, Ownership,
        MechanismController, AuthorityBaseOf,
        ClaimTCBOf, ExternalReliesOf)

ASSUME GuaranteeRecordsHeld ==
    GuaranteeRecordsTyped(
        Frames, Principals, EvidenceItems, Mechanisms,
        Assumptions, Ceilings, Guarantees, Ownership,
        ClaimTCBOf, GuaranteeFrame, GuaranteeIssuer,
        GuaranteeRecipient, GuaranteeEvidence,
        GuaranteeRelies, GuaranteeTCB, GuaranteeCeiling)

ASSUME ClaimRecordsSeparated ==
    ClaimRecordSeparation(
        Frames, Principals, Guarantees, Ownership,
        GuaranteeFrame, GuaranteeIssuer,
        Assurances, AssuranceFrame, AssuranceClaimant)

THEOREM OneOwnerAtMostPerFrame ==
    \A frame \in Frames :
      \A first \in OwnersOf(frame, Principals, Ownership) :
        \A second \in OwnersOf(frame, Principals, Ownership) :
          first = second
BY SMT, CompleteOwnershipHeld
   DEF CompleteOwnershipDisposition, CanonicalOwnershipTyped,
       SingleOwnerPerFrame, OwnersOf

THEOREM EveryRecordedOwnerCoversTheFrame ==
    \A pair \in Ownership :
      Covers(pair[1], pair[2], DecisiveOf, ControlsOf, ExcludesOf)
BY SMT, CompleteOwnershipHeld
   DEF CompleteOwnershipDisposition, CanonicalOwnershipTyped

THEOREM NoEligibleOwnerMeansNoOwner ==
    \A frame \in Frames :
      EligibleOwners(
          frame, Principals,
          DecisiveOf, ControlsOf, ExcludesOf) = {}
        => OwnersOf(frame, Principals, Ownership) = {}
BY SMT, CompleteOwnershipHeld
   DEF CompleteOwnershipDisposition, CanonicalOwnershipTyped,
       EligibleOwners, OwnersOf, Covers

THEOREM TechnicalAccountabilityFollowsOwnership ==
    Accountability = Ownership
BY SMT, TechnicalAccountabilityHeld DEF TechnicalAccountabilityTyped

THEOREM EveryGuaranteeNamesTheCanonicalOwner ==
    \A guarantee \in Guarantees :
      GuaranteeIssuer[guarantee]
        = CanonicalOwner(
              GuaranteeFrame[guarantee], Principals, Ownership)
BY SMT, GuaranteeRecordsHeld DEF GuaranteeRecordsTyped

THEOREM EveryGuaranteeCarriesItsClaimTCB ==
    \A guarantee \in Guarantees :
      GuaranteeTCB[guarantee]
        = ClaimTCBOf[GuaranteeFrame[guarantee]]
BY SMT, GuaranteeRecordsHeld DEF GuaranteeRecordsTyped

THEOREM ExternalReliesAreInsideTheClaimTCB ==
    \A frame \in Frames :
      /\ ExternalReliesOf[frame] \subseteq ClaimTCBOf[frame]
      /\ ExternalReliesOf[frame]
           = ClaimTCBOf[frame] \ AuthorityBaseOf[frame]
BY SMT, DependencyBoundariesHeld DEF DependencyBoundariesTyped

THEOREM NonOwnerAssuranceDoesNotBecomeAGuarantee ==
    \A assurance \in Assurances :
      LET frame == AssuranceFrame[assurance]
          claimant == AssuranceClaimant[assurance]
      IN
      frame \in OwnedFrames(Frames, Principals, Ownership)
        /\ claimant # CanonicalOwner(frame, Principals, Ownership)
        => \A guarantee \in Guarantees :
             GuaranteeFrame[guarantee] = frame
               => GuaranteeIssuer[guarantee] # claimant
BY SMT, ClaimRecordsSeparated DEF ClaimRecordSeparation

====
