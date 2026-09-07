---- MODULE ALKClaimAuthorityWitness ----
EXTENDS ALKClaimAuthorityBinding, ClaimAssuranceProfiles

ControlsOf == ControlsForMode("direct")

Ownership == DerivedOwnership("direct")

Accountability == Ownership

AuthorityBaseOf ==
    [frame \in Frames |->
        IF frame = BudgetFrame
          THEN {"budget-guard"}
        ELSE {"sequential-state-machine"}]

ClaimTCBOf ==
    [frame \in Frames |->
        IF frame = BudgetFrame
          THEN {"budget-guard", "worker-runtime", "claim-log"}
        ELSE {"sequential-state-machine"}]

ExternalReliesOf ==
    [frame \in Frames |-> ClaimTCBOf[frame] \ AuthorityBaseOf[frame]]

EvidenceItems ==
    {"attributed-assertion", "independent-readback", "monitor-event",
     "recovery-test", "owner-commit-record"}

Assumptions ==
    {"A-BUD", "A-SEQ", "worker-output-validated",
     "monitor-clock-and-coverage", "recovery-custody"}

Ceilings ==
    {"in-memory-no-crash-no-hidden-writer",
     "point-observation-only", "bounded-detection-only",
     "bounded-recovery-only"}

Guarantees == {"g-budget", "g-sequential"}

GuaranteeFrame ==
    [guarantee \in Guarantees |->
        IF guarantee = "g-budget" THEN BudgetFrame ELSE SequentialFrame]

GuaranteeIssuer ==
    [guarantee \in Guarantees |->
        IF guarantee = "g-budget"
          THEN "budget-authority"
        ELSE "sequential-authority"]

GuaranteeRecipient ==
    [guarantee \in Guarantees |-> "job-controller"]

GuaranteeEvidence ==
    [guarantee \in Guarantees |->
        IF guarantee = "g-budget"
          THEN {"owner-commit-record"}
        ELSE {}]

GuaranteeRelies ==
    [guarantee \in Guarantees |->
        IF guarantee = "g-budget"
          THEN {"A-BUD", "worker-output-validated"}
        ELSE {"A-SEQ"}]

GuaranteeTCB ==
    [guarantee \in Guarantees |-> ClaimTCBOf[GuaranteeFrame[guarantee]]]

GuaranteeCeiling ==
    [guarantee \in Guarantees |->
        "in-memory-no-crash-no-hidden-writer"]

Propositions ==
    {"request-recorded", "source-asserted-capacity",
     "capacity-observed", "capacity-divergence-detected",
     "capacity-state-recoverable", "capacity-owner-guarantee"}

ObservationTimes ==
    {"none", "assertion-time", "readback-time", "within-five-ticks",
     "within-two-hundred-forty-ticks", "at-commit"}

IndependenceClasses == {"none", "self-reported", "independent"}
Limits ==
    {"reliance-only", "assertion-not-truth", "point-observation",
     "detection-not-prevention", "recovery-not-continuous-correctness",
     "claimant-does-not-own"}

Assurances == {"a0", "a1", "a2", "a3", "a4", "a5"}

AssuranceFrame == [assurance \in Assurances |-> BudgetFrame]
AssuranceClaimant == [assurance \in Assurances |-> "job-controller"]
AssuranceSource ==
    [assurance \in Assurances |->
        CASE assurance \in {"a0", "a1", "a2", "a3", "a5"} ->
               "budget-authority"
          [] OTHER -> "recovery-provider"]
AssuranceVerifier ==
    [assurance \in Assurances |->
        IF assurance \in {"a2", "a3", "a4"}
          THEN "independent-auditor"
        ELSE "job-controller"]
AssuranceClassesOf ==
    [assurance \in Assurances |->
        CASE assurance = "a0" -> {"A0"}
          [] assurance = "a1" -> {"A1"}
          [] assurance = "a2" -> {"A2"}
          [] assurance = "a3" -> {"A3"}
          [] assurance = "a4" -> {"A4"}
          [] OTHER -> {"A5"}]
AssuranceEvidence ==
    [assurance \in Assurances |->
        CASE assurance = "a0" -> {}
          [] assurance = "a1" -> {"attributed-assertion"}
          [] assurance = "a2" -> {"independent-readback"}
          [] assurance = "a3" -> {"monitor-event"}
          [] assurance = "a4" -> {"recovery-test"}
          [] OTHER -> {"owner-commit-record"}]
AttributedEvidence == {"attributed-assertion", "owner-commit-record"}
IndependentEvidence ==
    {"independent-readback", "monitor-event", "recovery-test"}
AssuranceObservationTime ==
    [assurance \in Assurances |->
        CASE assurance = "a0" -> "none"
          [] assurance = "a1" -> "assertion-time"
          [] assurance = "a2" -> "readback-time"
          [] assurance = "a3" -> "within-five-ticks"
          [] assurance = "a4" -> "within-two-hundred-forty-ticks"
          [] OTHER -> "at-commit"]
DetectionBound ==
    [assurance \in Assurances |-> IF assurance = "a3" THEN 5 ELSE 0]
DetectionCoverage ==
    [assurance \in Assurances |->
        IF assurance = "a3" THEN DecisiveOf[BudgetFrame] ELSE {}]
RecoveryMechanisms ==
    [assurance \in Assurances |->
        IF assurance = "a4" THEN {"recovery-copy"} ELSE {}]
RecoveryPointBound ==
    [assurance \in Assurances |-> IF assurance = "a4" THEN 60 ELSE 0]
RecoveryTimeBound ==
    [assurance \in Assurances |-> IF assurance = "a4" THEN 240 ELSE 0]
OwnerGuarantees ==
    [assurance \in Assurances |->
        IF assurance = "a5" THEN {"g-budget"} ELSE {}]

AssuranceProposition ==
    [assurance \in Assurances |->
        CASE assurance = "a0" -> "request-recorded"
          [] assurance = "a1" -> "source-asserted-capacity"
          [] assurance = "a2" -> "capacity-observed"
          [] assurance = "a3" -> "capacity-divergence-detected"
          [] assurance = "a4" -> "capacity-state-recoverable"
          [] OTHER -> "capacity-owner-guarantee"]
AssuranceObservation == AssuranceObservationTime
AssuranceIndependence ==
    [assurance \in Assurances |->
        IF assurance \in {"a2", "a3", "a4"}
          THEN "independent"
        ELSE IF assurance = "a0" THEN "none" ELSE "self-reported"]
AssuranceLimits ==
    [assurance \in Assurances |->
        CASE assurance = "a0" -> {"reliance-only"}
          [] assurance = "a1" -> {"assertion-not-truth"}
          [] assurance = "a2" -> {"point-observation"}
          [] assurance = "a3" -> {"detection-not-prevention"}
          [] assurance = "a4" ->
               {"recovery-not-continuous-correctness"}
          [] OTHER -> {"claimant-does-not-own"}]

Delegations == {"d-budget-work", "d-budget-transfer"}
DelegationFrame == [delegation \in Delegations |-> BudgetFrame]
Delegator ==
    [delegation \in Delegations |-> "budget-authority"]
Delegate ==
    [delegation \in Delegations |->
        IF delegation = "d-budget-work"
          THEN "budget-worker"
        ELSE "successor-authority"]
DelegationKind ==
    [delegation \in Delegations |->
        IF delegation = "d-budget-work" THEN "work" ELSE "authority"]
DelegatedBehaviors ==
    [delegation \in Delegations |->
        IF delegation = "d-budget-work"
          THEN {"worker-compute"}
        ELSE DecisiveOf[BudgetFrame]]

TransferControlsOf == ControlsForMode("transfer")
TransferOwnership == DerivedOwnership("transfer")
TransferAccountability == TransferOwnership
TransferClaimTCBOf ==
    [frame \in Frames |->
        IF frame = BudgetFrame
          THEN {"successor-guard", "worker-runtime", "claim-log"}
        ELSE {"sequential-state-machine"}]
TransferGuarantees == {"g-budget-transfer"}
TransferGuaranteeFrame ==
    [guarantee \in TransferGuarantees |-> BudgetFrame]
TransferGuaranteeIssuer ==
    [guarantee \in TransferGuarantees |-> "successor-authority"]
TransferGuaranteeRecipient ==
    [guarantee \in TransferGuarantees |-> "job-controller"]
TransferGuaranteeEvidence ==
    [guarantee \in TransferGuarantees |-> {"owner-commit-record"}]
TransferGuaranteeRelies ==
    [guarantee \in TransferGuarantees |-> {"A-BUD"}]
TransferGuaranteeTCB ==
    [guarantee \in TransferGuarantees |-> TransferClaimTCBOf[BudgetFrame]]
TransferGuaranteeCeiling ==
    [guarantee \in TransferGuarantees |->
        "in-memory-no-crash-no-hidden-writer"]

SplitControlsOf == ControlsForMode("split")
SplitOwnership == DerivedOwnership("split")

ProtocolControlsOf == ControlsForMode("protocol")
ProtocolOwnership == DerivedOwnership("protocol")

OwnershipBoundaryHeld(candidateOwnership, candidateControlsOf) ==
    /\ AuthorityBindingsTyped(
           Frames, Principals, Behaviors,
           DecisiveOf, candidateControlsOf, ExcludesOf)
    /\ CompleteOwnershipDisposition(
           Frames, Principals, candidateOwnership,
           DecisiveOf, candidateControlsOf, ExcludesOf)

GuaranteeBoundaryHeld(
        candidateOwnership, candidateIssuer, candidateRecipient) ==
    GuaranteeRecordsTyped(
        Frames, Principals, EvidenceItems, Mechanisms,
        Assumptions, Ceilings, Guarantees, candidateOwnership,
        ClaimTCBOf, GuaranteeFrame, candidateIssuer,
        candidateRecipient, GuaranteeEvidence,
        GuaranteeRelies, GuaranteeTCB, GuaranteeCeiling)

AssuranceProfileBoundaryHeld(candidateClaimant) ==
    AssuranceProfilesTyped(
        Frames, Principals, Behaviors, EvidenceItems, Mechanisms,
        Guarantees, Ownership,
        GuaranteeFrame, GuaranteeIssuer, GuaranteeRecipient,
        Assurances, AssuranceFrame, candidateClaimant,
        AssuranceSource, AssuranceVerifier,
        AssuranceClassesOf, AssuranceEvidence,
        AttributedEvidence, IndependentEvidence,
        AssuranceObservationTime, DetectionBound,
        DetectionCoverage, RecoveryMechanisms,
        RecoveryPointBound, RecoveryTimeBound,
        OwnerGuarantees)

DirectOwnershipHeld == OwnershipBoundaryHeld(Ownership, ControlsOf)

TechnicalAccountabilityHeld ==
    TechnicalAccountabilityTyped(
        Frames, Principals, Ownership, Accountability)

DependencyBoundaryHeld ==
    DependencyBoundariesTyped(
        Frames, Principals, Mechanisms, Ownership,
        MechanismController, AuthorityBaseOf,
        ClaimTCBOf, ExternalReliesOf)

GuaranteeRecordsHeld ==
    GuaranteeBoundaryHeld(Ownership, GuaranteeIssuer, GuaranteeRecipient)

AssuranceRecordsHeld ==
    AssuranceRecordsTyped(
        Frames, Principals, Propositions, EvidenceItems,
        ObservationTimes, IndependenceClasses, Limits,
        Assurances, AssuranceFrame, AssuranceClaimant,
        AssuranceSource, AssuranceProposition,
        AssuranceEvidence, AssuranceObservation,
        AssuranceIndependence, AssuranceLimits)

AllAssuranceProfilesHeld ==
    /\ AssuranceProfileBoundaryHeld(AssuranceClaimant)
    /\ {AssuranceClassesOf[assurance] : assurance \in Assurances}
         = {{"A0"}, {"A1"}, {"A2"}, {"A3"}, {"A4"}, {"A5"}}
    /\ \A assurance \in Assurances :
          NonOrdinalAssuranceProfile(assurance, AssuranceClassesOf)

DelegationRecordsHeld ==
    DelegationRecordsTyped(
        Frames, Principals, Behaviors, Delegations,
        DelegationFrame, Delegator, Delegate,
        DelegationKind, DelegatedBehaviors)

WorkDelegationPreservesOwnership ==
    /\ OwnershipPreservingDelegation(
           "d-budget-work", Frames, Principals, Ownership,
           DelegationFrame, Delegator, DelegationKind,
           DecisiveOf, ControlsOf, ExcludesOf)
    /\ DelegatedBehaviors["d-budget-work"]
         \cap DecisiveOf[BudgetFrame] = {}

CompleteAuthorityTransferHeld ==
    /\ OwnershipBoundaryHeld(TransferOwnership, TransferControlsOf)
    /\ TechnicalAccountabilityTyped(
           Frames, Principals, TransferOwnership,
           TransferAccountability)
    /\ OwnershipTransferResult(
           "d-budget-transfer", Frames, Principals,
           TransferOwnership, TransferAccountability,
           DelegationFrame, Delegator, Delegate, DelegationKind,
           DecisiveOf, TransferControlsOf, ExcludesOf)
    /\ GuaranteeRecordsTyped(
           Frames, Principals, EvidenceItems, Mechanisms,
           Assumptions, Ceilings, TransferGuarantees,
           TransferOwnership, TransferClaimTCBOf,
           TransferGuaranteeFrame, TransferGuaranteeIssuer,
           TransferGuaranteeRecipient, TransferGuaranteeEvidence,
           TransferGuaranteeRelies, TransferGuaranteeTCB,
           TransferGuaranteeCeiling)
    /\ \A guarantee \in TransferGuarantees :
          TransferGuaranteeIssuer[guarantee] # "budget-authority"

SplitAuthorityUnowned ==
    /\ OwnershipBoundaryHeld(SplitOwnership, SplitControlsOf)
    /\ EligibleOwners(
           BudgetFrame, Principals, DecisiveOf,
           SplitControlsOf, ExcludesOf) = {}
    /\ BudgetFrame \in UnownedFrames(
           Frames, Principals, SplitOwnership)

ProtocolIsOneOwner ==
    /\ OwnershipBoundaryHeld(ProtocolOwnership, ProtocolControlsOf)
    /\ OwnersOf(BudgetFrame, Principals, ProtocolOwnership)
         = {"alk-protocol"}
    /\ ProtocolMembers
         \cap OwnersOf(BudgetFrame, Principals, ProtocolOwnership) = {}

DistributedObligationsUseDifferentOwners ==
    CanonicalOwner(BudgetFrame, Principals, Ownership)
      # CanonicalOwner(SequentialFrame, Principals, Ownership)

ClaimAuthorityHeld ==
    /\ ClaimInstantiationHeld
    /\ DirectOwnershipHeld
    /\ TechnicalAccountabilityHeld
    /\ DependencyBoundaryHeld
    /\ GuaranteeRecordsHeld
    /\ AssuranceRecordsHeld
    /\ AllAssuranceProfilesHeld
    /\ DelegationRecordsHeld
    /\ WorkDelegationPreservesOwnership
    /\ CompleteAuthorityTransferHeld
    /\ SplitAuthorityUnowned
    /\ ProtocolIsOneOwner
    /\ DistributedObligationsUseDifferentOwners

====
