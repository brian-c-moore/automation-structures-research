---- MODULE ALKClaimAssuranceBindingWitness ----
EXTENDS ALKClaimEvidenceWitness, ClaimEvidenceBinding

\* The diagnostic protocol owns its finite capture/monitor/restore actions.
\* The corrupting source owns the fault injection. Fair execution of the
\* protocol's tick action is an explicit temporal premise; no clock premise
\* is inferred from a positive bound or from enabledness.
DiagnosticLabels == {"capture", "fault", "monitor", "restore", "done"}
DiagnosticController(label) ==
    IF label = "fault" THEN "budget-authority" ELSE "alk-protocol"
DiagnosticDecision(label) ==
    IF label = "fault" THEN {"budget-authority"}
    ELSE {"independent-auditor", "recovery-provider", "job-controller"}
DiagnosticAction(label) ==
    CASE label = "capture" -> Capture
      [] label = "fault" -> InjectPersistentOverallocation
      [] label = "monitor" -> MonitorTick(TRUE)
      [] label = "restore" -> RecoveryTick(TRUE)
      [] OTHER -> EvidenceDone
DiagnosticGate(label, actor, decision) ==
    /\ actor = DiagnosticController(label)
    /\ decision = DiagnosticDecision(label)
    /\ DiagnosticAction(label)
DiagnosticNext ==
    \E label \in DiagnosticLabels :
        DiagnosticGate(label, DiagnosticController(label), DiagnosticDecision(label))

BindingFrames == Frames \cup {EvidenceClaimFrame, DetectionFrame, RecoveryFrame}
DiagnosticFrames == {EvidenceClaimFrame, DetectionFrame, RecoveryFrame}
DiagnosticDecisiveOf ==
    [frame \in DiagnosticFrames |->
        IF frame = EvidenceClaimFrame THEN {"capture", "monitor", "restore"}
        ELSE IF frame = DetectionFrame THEN {"monitor", "restore"}
        ELSE {"capture", "monitor", "restore"}]
DiagnosticControls ==
    [frame \in DiagnosticFrames |->
        [principal \in Principals |->
            {label \in DiagnosticDecisiveOf[frame] :
                DiagnosticController(label) = principal}]]
DiagnosticExcludes ==
    [frame \in DiagnosticFrames |-> [principal \in Principals |-> {}]]
DiagnosticOwnership ==
    {pair \in DiagnosticFrames \X Principals :
        /\ pair[2] = "alk-protocol"
        /\ pair[2] \in EligibleOwners(pair[1], Principals,
            DiagnosticDecisiveOf, DiagnosticControls, DiagnosticExcludes)}
BindingOwnership == DerivedOwnership("direct") \cup DiagnosticOwnership

RecordSourceFor(class) ==
    IF class \in {"A3", "A4"} THEN "alk-protocol" ELSE "budget-authority"
RecordVerifierFor(class) ==
    IF class \in {"A2", "A3", "A4"} THEN "independent-auditor" ELSE "job-controller"
RecordProducerFor(class) ==
    CASE class \in {"A2", "A3"} -> "independent-auditor"
      [] class = "A4" -> "recovery-provider"
      [] OTHER -> "budget-authority"
RecordObservationFor(class) ==
    CASE class = "A0" -> "none"
      [] class = "A3" -> "tick-three"
      [] class = "A4" -> "tick-five"
      [] OTHER -> "tick-zero"
RecordLimitFor(class) ==
    CASE class = "A0" -> {"reliance-only"}
      [] class = "A1" -> {"assertion-not-truth"}
      [] class = "A2" -> {"point-observation"}
      [] class = "A3" -> {"detection-not-prevention"}
      [] class = "A4" -> {"recovery-not-continuous-correctness"}
      [] OTHER -> {"claimant-does-not-own", "claim-at-capture-only"}
RecordKindFor(class) ==
    CASE class = "A1" -> "attribution"
      [] class = "A2" -> "observation"
      [] class = "A3" -> "detection"
      [] class = "A4" -> "restoration"
      [] OTHER -> "owner-record"

BindingRecords ==
    [class \in ActiveClasses |->
        [id |-> class, frame |-> ClassFrame(class),
         claimant |-> "job-controller", source |-> RecordSourceFor(class),
         verifier |-> RecordVerifierFor(class), classes |-> {class},
         proposition |-> ClassClaim(class),
         evidence |-> IF class = "A0" THEN {} ELSE {class},
         observation |-> RecordObservationFor(class),
         limits |-> RecordLimitFor(class),
         mechanismFrame |-> ClassFrame(class),
         mechanismClaims |-> IF class \in {"A3", "A4", "A5"} THEN {class} ELSE {},
         detectionBound |-> 2, recoveryTimeBound |-> 4, recoveryPointBound |-> 1]]

BindingEvidence ==
    [class \in ActiveClasses \ {"A0"} |->
        [id |-> class, frame |-> ClassFrame(class),
         proposition |-> ClassClaim(class), claimant |-> "job-controller",
         source |-> RecordSourceFor(class), verifier |-> RecordVerifierFor(class),
         producer |-> RecordProducerFor(class), observation |-> RecordObservationFor(class),
         custody |-> IF snapshotRetained THEN "retained" ELSE "lost",
         kind |-> RecordKindFor(class),
         coverage |-> IF class = "A3" THEN {"persistent-overallocation"} ELSE {},
         elapsed |-> IF class = "A3" THEN 2 ELSE IF class = "A4" THEN 4 ELSE 0,
         snapshotAge |-> IF class = "A4" THEN 1 ELSE 0]]

BindingEvidenceSemantics ==
    [class \in DOMAIN BindingEvidence |->
        CASE class = "A1" -> RecordedObservationExists /\ RecordMetadataHeld
          [] class \in {"A2", "A5"} -> CapturedObservationHeld /\ RecordMetadataHeld
          [] class = "A3" -> alarmRaised /\ DetectionBoundHeld
          [] OTHER -> RecoveredSnapshotHeld /\ RecoveryBoundHeld]

BindingGuarantees ==
    [class \in ActiveClasses \cap {"A3", "A4", "A5"} |->
        [id |-> class, frame |-> ClassFrame(class),
         issuer |-> IF class = "A5" THEN "budget-authority" ELSE "alk-protocol",
         recipient |-> "job-controller",
         predicate |-> CASE class = "A3" -> "DetectionBoundHeld"
                         [] class = "A4" -> "RecoveredSnapshotHeld"
                         [] OTHER -> "CapturedContract!SafetyInvariant",
         relies |-> IF class = "A5"
                      THEN {"atomic-capture", "authentic-source", "claim-at-capture-only"}
                    ELSE {"fair-logical-clock", "atomic-read", "retained-store", "one-persistent-fault"},
         tcb |-> IF class = "A5" THEN {"budget-guard", "claim-log"}
                 ELSE {"diagnostic-gate", "clock-service", "snapshot-store"},
         qualifiers |-> {"conditional"}, outcome |-> "holds"]]
BindingGuaranteeSemantics ==
    [class \in DOMAIN BindingGuarantees |->
        CASE class = "A3" -> alarmRaised /\ DetectionBoundHeld
          [] class = "A4" -> stateRecovered /\ RecoveredSnapshotHeld
          [] OTHER -> CapturedObservationHeld /\ RecordMetadataHeld]

VARIABLE bindingFault
bindingVars == <<evidenceVars, bindingFault>>
BindingInit == EvidenceInit /\ bindingFault = "none"
BindingNext == DiagnosticNext /\ UNCHANGED bindingFault
BindingSpec ==
    BindingInit /\ [][BindingNext]_bindingVars /\ WF_bindingVars(BindingNext)

EffectiveBindingEvidence ==
    CASE bindingFault = "wrong-proposition" ->
           [BindingEvidence EXCEPT !["A2"].proposition = "arbitrary-unobserved-proposition"]
      [] bindingFault = "wrong-producer" ->
           [BindingEvidence EXCEPT !["A2"].producer = "budget-authority"]
      [] bindingFault = "wrong-frame" ->
           [BindingEvidence EXCEPT !["A2"].frame = SequentialFrame]
      [] OTHER -> BindingEvidence
EffectiveBindingSemantics ==
    IF bindingFault = "failed-semantics"
      THEN [BindingEvidenceSemantics EXCEPT !["A2"] = FALSE]
    ELSE BindingEvidenceSemantics
EffectiveBindingGuarantees ==
    CASE bindingFault = "wrong-mechanism-frame" ->
           [BindingGuarantees EXCEPT !["A3"].frame = RecoveryFrame]
      [] bindingFault = "wrong-issuer" ->
           [BindingGuarantees EXCEPT !["A3"].issuer = "budget-authority"]
      [] OTHER -> BindingGuarantees
SharedClaimBindingHeld ==
    BoundClaimRecords(BindingFrames, Principals, BindingOwnership,
        BindingRecords, EffectiveBindingEvidence, EffectiveBindingSemantics,
        EffectiveBindingGuarantees, BindingGuaranteeSemantics)
DiagnosticAuthorityHeld ==
    /\ CompleteOwnershipDisposition(DiagnosticFrames, Principals, DiagnosticOwnership,
           DiagnosticDecisiveOf, DiagnosticControls, DiagnosticExcludes)
    /\ \A frame \in DiagnosticFrames :
          OwnersOf(frame, Principals, DiagnosticOwnership) = {"alk-protocol"}
BindingInvariant ==
    /\ EvidenceInvariant /\ DiagnosticAuthorityHeld /\ SharedClaimBindingHeld
====
