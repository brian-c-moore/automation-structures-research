---- MODULE ClaimRelativeOwnershipControlBase ----
EXTENDS ClaimRelativeOwnershipWitness

ControlModes ==
    {"none", "shared-owner", "assurance-credit",
     "non-owner-issuer", "work-transfer"}

VARIABLE controlMode

controlVars == <<witness, controlMode>>

ControlInit ==
    /\ Init
    /\ controlMode = "none"

GoodNext == UNCHANGED controlVars

Inject(mode) ==
    /\ controlMode = "none"
    /\ mode \in ControlModes \ {"none"}
    /\ controlMode' = mode
    /\ UNCHANGED witness

EffectiveOwnership ==
    CASE controlMode = "shared-owner" ->
           Ownership \cup {<<SystemFrame, "component">>}
      [] controlMode = "assurance-credit" ->
           Ownership
             \cup {<<EndToEndFrame,
                      AssuranceClaimant["a-end-to-end"]>>}
      [] controlMode = "work-transfer" ->
           (Ownership \ {<<ComponentFrame, "component">>})
             \cup {<<ComponentFrame, "worker">>}
      [] OTHER -> Ownership

EffectiveGuaranteeIssuer ==
    [guarantee \in Guarantees |->
        IF /\ controlMode = "non-owner-issuer"
           /\ guarantee = "g-system"
          THEN "organization"
          ELSE GuaranteeIssuer[guarantee]]

SharedOwnerRejected ==
    CanonicalOwnershipTyped(
        Frames, Principals, EffectiveOwnership,
        DecisiveOf, ControlsOf, ExcludesOf)

AssuranceCreditRejected ==
    CanonicalOwnershipTyped(
        Frames, Principals, EffectiveOwnership,
        DecisiveOf, ControlsOf, ExcludesOf)

NonOwnerIssuerRejected ==
    GuaranteeRecordsTyped(
        Frames, Principals, EvidenceItems, Mechanisms,
        Assumptions, Ceilings, Guarantees, Ownership,
        ClaimTCBOf, GuaranteeFrame, EffectiveGuaranteeIssuer,
        GuaranteeRecipient, GuaranteeEvidence,
        GuaranteeRelies, GuaranteeTCB, GuaranteeCeiling)

WorkDelegationTransfersRejected ==
    OwnershipPreservingDelegation(
        "d-work", Frames, Principals, EffectiveOwnership,
        DelegationFrame, Delegator, DelegationKind,
        DecisiveOf, ControlsOf, ExcludesOf)

====
