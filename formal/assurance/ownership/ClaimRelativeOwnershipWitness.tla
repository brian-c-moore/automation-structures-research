---- MODULE ClaimRelativeOwnershipWitness ----
EXTENDS ClaimRelativeOwnership

Principals ==
    {"algorithm-protocol", "component", "alk-protocol",
     "custodian", "organization", "worker", "auditor"}

AlgorithmFrame ==
    [subject |-> "selection-state",
     obligation |-> "selection-integrity",
     mode |-> "ranked",
     scope |-> "one-selection",
     observationBoundary |-> "algorithm-state",
     authorityBoundary |-> "algorithm-protocol-boundary",
     claimant |-> "component",
     failureModel |-> "modeled-transition-faults",
     abstraction |-> "algorithm",
     lifecyclePhase |-> "use",
     propertyForm |-> "safety"]

ComponentFrame ==
    [subject |-> "selection-component",
     obligation |-> "bounded-admission",
     mode |-> "ranked",
     scope |-> "one-component-instance",
     observationBoundary |-> "component-commits",
     authorityBoundary |-> "component-boundary",
     claimant |-> "alk-protocol",
     failureModel |-> "worker-failure",
     abstraction |-> "component",
     lifecyclePhase |-> "use",
     propertyForm |-> "safety"]

SystemFrame ==
    [subject |-> "automation-system",
     obligation |-> "mediated-execution",
     mode |-> "governed",
     scope |-> "one-plan",
     observationBoundary |-> "kernel-events",
     authorityBoundary |-> "alk-boundary",
     claimant |-> "organization",
     failureModel |-> "component-failure",
     abstraction |-> "system",
     lifecyclePhase |-> "use",
     propertyForm |-> "safety"]

CustodyFrame ==
    [subject |-> "external-record",
     obligation |-> "record-retention",
     mode |-> "retained",
     scope |-> "one-record",
     observationBoundary |-> "custody-evidence",
     authorityBoundary |-> "custodian-boundary",
     claimant |-> "organization",
     failureModel |-> "storage-failure",
     abstraction |-> "service",
     lifecyclePhase |-> "retention",
     propertyForm |-> "evidence"]

EndToEndFrame ==
    [subject |-> "automated-retention-flow",
     obligation |-> "execute-and-retain",
     mode |-> "external-custody",
     scope |-> "one-execution-record",
     observationBoundary |-> "system-and-custody-evidence",
     authorityBoundary |-> "split-authority",
     claimant |-> "organization",
     failureModel |-> "kernel-or-storage-failure",
     abstraction |-> "system-of-systems",
     lifecyclePhase |-> "use-and-retention",
     propertyForm |-> "evidence"]

GovernanceFrame ==
    [subject |-> "governed-data",
     obligation |-> "classification-and-risk",
     mode |-> "organizational",
     scope |-> "one-data-class",
     observationBoundary |-> "governance-record",
     authorityBoundary |-> "organization-boundary",
     claimant |-> "auditor",
     failureModel |-> "policy-failure",
     abstraction |-> "organization",
     lifecyclePhase |-> "lifecycle",
     propertyForm |-> "evidence"]

Frames ==
    {AlgorithmFrame, ComponentFrame, SystemFrame,
     CustodyFrame, EndToEndFrame, GovernanceFrame}

Subjects == {frame.subject : frame \in Frames}
Obligations == {frame.obligation : frame \in Frames}
Modes == {frame.mode : frame \in Frames}
Scopes == {frame.scope : frame \in Frames}
ObservationBoundaries ==
    {frame.observationBoundary : frame \in Frames}
AuthorityBoundaries ==
    {frame.authorityBoundary : frame \in Frames}
Claimants == {frame.claimant : frame \in Frames}
FailureModels == {frame.failureModel : frame \in Frames}
Abstractions == {frame.abstraction : frame \in Frames}
LifecyclePhases == {frame.lifecyclePhase : frame \in Frames}

Behaviors ==
    {"select", "commit", "schedule", "retain", "classify", "compute"}

DecisiveOf ==
    [frame \in Frames |->
        CASE frame = AlgorithmFrame -> {"select"}
          [] frame = ComponentFrame -> {"commit"}
          [] frame = SystemFrame -> {"schedule"}
          [] frame = CustodyFrame -> {"retain"}
          [] frame = EndToEndFrame -> {"schedule", "retain"}
          [] OTHER -> {"classify"}]

ControlsOf ==
    [frame \in Frames |->
      [principal \in Principals |->
        CASE /\ frame = AlgorithmFrame
             /\ principal = "algorithm-protocol" -> {"select"}
          [] /\ frame = ComponentFrame
             /\ principal = "component" -> {"commit"}
          [] /\ frame = SystemFrame
             /\ principal = "alk-protocol" -> {"schedule"}
          [] /\ frame = CustodyFrame
             /\ principal = "custodian" -> {"retain"}
          [] /\ frame = EndToEndFrame
             /\ principal = "alk-protocol" -> {"schedule"}
          [] /\ frame = EndToEndFrame
             /\ principal = "custodian" -> {"retain"}
          [] /\ frame = GovernanceFrame
             /\ principal = "organization" -> {"classify"}
          [] OTHER -> {}]]

ExcludesOf ==
    [frame \in Frames |-> [principal \in Principals |-> {}]]

Ownership ==
    {<<AlgorithmFrame, "algorithm-protocol">>,
     <<ComponentFrame, "component">>,
     <<SystemFrame, "alk-protocol">>,
     <<CustodyFrame, "custodian">>,
     <<GovernanceFrame, "organization">>}

Accountability == Ownership

Mechanisms ==
    {"algorithm-code", "component-guard", "alk-kernel",
     "object-store", "governance-policy", "worker-library"}

MechanismController ==
    [mechanism \in Mechanisms |->
        CASE mechanism = "algorithm-code" -> "algorithm-protocol"
          [] mechanism = "component-guard" -> "component"
          [] mechanism = "alk-kernel" -> "alk-protocol"
          [] mechanism = "object-store" -> "custodian"
          [] mechanism = "governance-policy" -> "organization"
          [] OTHER -> "worker"]

AuthorityBaseOf ==
    [frame \in Frames |->
        CASE frame = AlgorithmFrame -> {"algorithm-code"}
          [] frame = ComponentFrame -> {"component-guard"}
          [] frame = SystemFrame -> {"alk-kernel"}
          [] frame = CustodyFrame -> {"object-store"}
          [] frame = GovernanceFrame -> {"governance-policy"}
          [] OTHER -> {}]

ClaimTCBOf ==
    [frame \in Frames |->
        CASE frame = AlgorithmFrame -> {"algorithm-code"}
          [] frame = ComponentFrame ->
               {"component-guard", "worker-library"}
          [] frame = SystemFrame ->
               {"alk-kernel", "component-guard"}
          [] frame = CustodyFrame -> {"object-store"}
          [] frame = EndToEndFrame -> {"alk-kernel", "object-store"}
          [] OTHER -> {"governance-policy", "object-store"}]

ExternalReliesOf ==
    [frame \in Frames |-> ClaimTCBOf[frame] \ AuthorityBaseOf[frame]]

EvidenceItems ==
    {"selection-proof", "commit-record", "kernel-trace",
     "custody-receipt", "governance-record", "worker-result"}
Assumptions ==
    {"typed-input", "worker-available", "host-correct",
     "storage-available", "policy-authorized"}
Ceilings ==
    {"modeled-transition", "worker-failure", "component-failure",
     "storage-failure", "policy-failure"}

Guarantees ==
    {"g-algorithm", "g-component", "g-system",
     "g-custody", "g-governance"}

GuaranteeFrame ==
    [guarantee \in Guarantees |->
        CASE guarantee = "g-algorithm" -> AlgorithmFrame
          [] guarantee = "g-component" -> ComponentFrame
          [] guarantee = "g-system" -> SystemFrame
          [] guarantee = "g-custody" -> CustodyFrame
          [] OTHER -> GovernanceFrame]

GuaranteeIssuer ==
    [guarantee \in Guarantees |->
        CASE guarantee = "g-algorithm" -> "algorithm-protocol"
          [] guarantee = "g-component" -> "component"
          [] guarantee = "g-system" -> "alk-protocol"
          [] guarantee = "g-custody" -> "custodian"
          [] OTHER -> "organization"]

GuaranteeRecipient ==
    [guarantee \in Guarantees |->
        CASE guarantee = "g-algorithm" -> "component"
          [] guarantee = "g-component" -> "alk-protocol"
          [] guarantee = "g-system" -> "organization"
          [] guarantee = "g-custody" -> "organization"
          [] OTHER -> "auditor"]

GuaranteeEvidence ==
    [guarantee \in Guarantees |->
        CASE guarantee = "g-algorithm" -> {"selection-proof"}
          [] guarantee = "g-component" -> {"commit-record"}
          [] guarantee = "g-system" -> {"kernel-trace"}
          [] guarantee = "g-custody" -> {"custody-receipt"}
          [] OTHER -> {"governance-record"}]

GuaranteeRelies ==
    [guarantee \in Guarantees |->
        CASE guarantee = "g-algorithm" -> {"typed-input"}
          [] guarantee = "g-component" -> {"worker-available"}
          [] guarantee = "g-system" -> {"host-correct"}
          [] guarantee = "g-custody" -> {"storage-available"}
          [] OTHER -> {"policy-authorized"}]

GuaranteeTCB ==
    [guarantee \in Guarantees |-> ClaimTCBOf[GuaranteeFrame[guarantee]]]

GuaranteeCeiling ==
    [guarantee \in Guarantees |->
        CASE guarantee = "g-algorithm" -> "modeled-transition"
          [] guarantee = "g-component" -> "worker-failure"
          [] guarantee = "g-system" -> "component-failure"
          [] guarantee = "g-custody" -> "storage-failure"
          [] OTHER -> "policy-failure"]

Propositions ==
    {"record-retained", "worker-result-valid", "end-to-end-supported"}
ObservationTimes == {"precommit", "at-commit", "postcommit"}
IndependenceClasses == {"self-reported", "independent"}
Limits ==
    {"provider-trust", "point-observation", "no-end-to-end-owner"}

Assurances == {"a-custody", "a-worker", "a-end-to-end"}

AssuranceFrame ==
    [assurance \in Assurances |->
        CASE assurance = "a-custody" -> CustodyFrame
          [] assurance = "a-worker" -> ComponentFrame
          [] OTHER -> EndToEndFrame]

AssuranceClaimant ==
    [assurance \in Assurances |->
        CASE assurance = "a-custody" -> "organization"
          [] assurance = "a-worker" -> "alk-protocol"
          [] OTHER -> "organization"]

AssuranceSource ==
    [assurance \in Assurances |->
        CASE assurance = "a-custody" -> "custodian"
          [] assurance = "a-worker" -> "worker"
          [] OTHER -> "custodian"]

AssuranceProposition ==
    [assurance \in Assurances |->
        CASE assurance = "a-custody" -> "record-retained"
          [] assurance = "a-worker" -> "worker-result-valid"
          [] OTHER -> "end-to-end-supported"]

AssuranceEvidence ==
    [assurance \in Assurances |->
        CASE assurance = "a-custody" -> {"custody-receipt"}
          [] assurance = "a-worker" -> {"worker-result"}
          [] OTHER -> {"kernel-trace", "custody-receipt"}]

AssuranceObservation ==
    [assurance \in Assurances |->
        CASE assurance = "a-worker" -> "precommit"
          [] OTHER -> "postcommit"]

AssuranceIndependence ==
    [assurance \in Assurances |->
        IF assurance = "a-end-to-end"
          THEN "independent" ELSE "self-reported"]

AssuranceLimits ==
    [assurance \in Assurances |->
        CASE assurance = "a-custody" -> {"provider-trust"}
          [] assurance = "a-worker" -> {"point-observation"}
          [] OTHER -> {"no-end-to-end-owner"}]

Delegations == {"d-work", "d-custody"}

DelegationFrame ==
    [delegation \in Delegations |->
        IF delegation = "d-work" THEN ComponentFrame ELSE CustodyFrame]

Delegator ==
    [delegation \in Delegations |->
        IF delegation = "d-work" THEN "component" ELSE "organization"]

Delegate ==
    [delegation \in Delegations |->
        IF delegation = "d-work" THEN "worker" ELSE "custodian"]

DelegationKind ==
    [delegation \in Delegations |->
        IF delegation = "d-work" THEN "work" ELSE "authority"]

DelegatedBehaviors ==
    [delegation \in Delegations |->
        IF delegation = "d-work" THEN {"compute"} ELSE {"retain"}]

RefinesTo ==
    {<<AlgorithmFrame, ComponentFrame>>, <<ComponentFrame, SystemFrame>>}

ComposesInto ==
    {<<SystemFrame, EndToEndFrame>>, <<CustodyFrame, EndToEndFrame>>}

ClaimFramesHeld ==
    ClaimFramesTyped(
        Frames, Subjects, Obligations, Modes, Scopes,
        ObservationBoundaries, AuthorityBoundaries,
        Claimants, FailureModels, Abstractions, LifecyclePhases)

AuthorityBindingsHeld ==
    AuthorityBindingsTyped(
        Frames, Principals, Behaviors,
        DecisiveOf, ControlsOf, ExcludesOf)

CompleteOwnershipHeld ==
    CompleteOwnershipDisposition(
        Frames, Principals, Ownership,
        DecisiveOf, ControlsOf, ExcludesOf)

TechnicalAccountabilityHeld ==
    TechnicalAccountabilityTyped(
        Frames, Principals, Ownership, Accountability)

DependencyBoundariesHeld ==
    DependencyBoundariesTyped(
        Frames, Principals, Mechanisms, Ownership,
        MechanismController, AuthorityBaseOf,
        ClaimTCBOf, ExternalReliesOf)

GuaranteeRecordsHeld ==
    GuaranteeRecordsTyped(
        Frames, Principals, EvidenceItems, Mechanisms,
        Assumptions, Ceilings, Guarantees, Ownership,
        ClaimTCBOf, GuaranteeFrame, GuaranteeIssuer,
        GuaranteeRecipient, GuaranteeEvidence,
        GuaranteeRelies, GuaranteeTCB, GuaranteeCeiling)

AssuranceRecordsHeld ==
    AssuranceRecordsTyped(
        Frames, Principals, Propositions, EvidenceItems,
        ObservationTimes, IndependenceClasses, Limits,
        Assurances, AssuranceFrame, AssuranceClaimant,
        AssuranceSource, AssuranceProposition,
        AssuranceEvidence, AssuranceObservation,
        AssuranceIndependence, AssuranceLimits)

DelegationRecordsHeld ==
    DelegationRecordsTyped(
        Frames, Principals, Behaviors, Delegations,
        DelegationFrame, Delegator, Delegate,
        DelegationKind, DelegatedBehaviors)

AbstractionRelationsHeld ==
    AbstractionRelationsTyped(Frames, RefinesTo, ComposesInto)

WorkDelegationPreservesOwnership ==
    OwnershipPreservingDelegation(
        "d-work", Frames, Principals, Ownership,
        DelegationFrame, Delegator, DelegationKind,
        DecisiveOf, ControlsOf, ExcludesOf)

CustodyTransferMovesOwnership ==
    OwnershipTransferResult(
        "d-custody", Frames, Principals, Ownership, Accountability,
        DelegationFrame, Delegator, Delegate, DelegationKind,
        DecisiveOf, ControlsOf, ExcludesOf)

ClaimRecordsSeparated ==
    ClaimRecordSeparation(
        Frames, Principals, Guarantees, Ownership,
        GuaranteeFrame, GuaranteeIssuer,
        Assurances, AssuranceFrame, AssuranceClaimant)

EndToEndUnowned ==
    OwnersOf(EndToEndFrame, Principals, Ownership) = {}

RelatedFramesUseDifferentOwners ==
    /\ CanonicalOwner(AlgorithmFrame, Principals, Ownership)
         # CanonicalOwner(ComponentFrame, Principals, Ownership)
    /\ CanonicalOwner(ComponentFrame, Principals, Ownership)
         # CanonicalOwner(SystemFrame, Principals, Ownership)
    /\ CanonicalOwner(SystemFrame, Principals, Ownership)
         # CanonicalOwner(GovernanceFrame, Principals, Ownership)

VARIABLE witness

vars == <<witness>>

Init == witness = 0

Next == UNCHANGED vars

Spec == Init /\ [][Next]_vars

====
