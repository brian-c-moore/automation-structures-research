---- MODULE ALKClaimEvidenceWitness ----
EXTENDS ALKClaimAuthorityBinding, ClaimAssuranceProfiles

\* A finite diagnostic/custody specialization. The failure injection is
\* OUTSIDE BudgetFrame's no-hidden-writer contract. Its observation precedes
\* that fault; diagnostic guarantees use distinct frames. Ticks are modeled
\* clock events, not wall-clock seconds. Fair clock service, authentic
\* principal labels, atomic snapshot capture, and trusted retained storage
\* are premises. The toy AuditSink hash is not a cryptographic certificate.
VARIABLES evidenceLog, evidenceHash, evidencePhase, diagnosticTick,
          alarmRaised, stateRecovered, snapshotRetained, capturedBudget,
          recordFrame, recordSource, recordClaimant,
          assertCurrentTruth, observeCurrentTruth

evidenceVars ==
    <<vars, evidenceLog, evidenceHash, evidencePhase, diagnosticTick,
      alarmRaised, stateRecovered, snapshotRetained, capturedBudget,
      recordFrame, recordSource, recordClaimant,
      assertCurrentTruth, observeCurrentTruth>>

AuditHash(previous, operation) == (previous * 3 + operation + 1) % 100

Audit == INSTANCE AuditSink WITH Operations <- {1}, MaxLogLen <- 1,
    Hash <- AuditHash, log <- evidenceLog, last_hash <- evidenceHash

CapturedContract == INSTANCE Budget WITH Capacity <- 2,
    capacity <- capturedBudget[1], allocated <- capturedBudget[2],
    reserved <- capturedBudget[3], pending_eviction <- capturedBudget[4]

EvidenceClaimFrame ==
    [BudgetFrame EXCEPT
        !.obligation = "retained-budget-observation",
        !.observationBoundary = "one-bound-snapshot-and-custody-record",
        !.authorityBoundary = "capture-binding-retention-retrieval",
        !.failureModel = "atomic-capture-authentic-labels-retained-store",
        !.abstraction = "claim-evidence-path",
        !.lifecyclePhase = "retention",
        !.propertyForm = "evidence"]

DetectionFrame ==
    [BudgetFrame EXCEPT
        !.obligation = "detect-single-overallocation",
        !.observationBoundary = "complete-budget-ledger-and-logical-clock",
        !.authorityBoundary = "monitor-read-and-clock-service",
        !.failureModel = "one-persistent-overallocation-fair-trusted-clock",
        !.abstraction = "bounded-diagnostic",
        !.propertyForm = "liveness"]

RecoveryFrame ==
    [DetectionFrame EXCEPT
        !.obligation = "restore-captured-budget",
        !.authorityBoundary = "snapshot-custody-restore-and-clock-service",
        !.abstraction = "bounded-snapshot-restoration",
        !.lifecyclePhase = "recovery"]

EvidenceDecisive == {"capture", "bind", "retain", "retrieve"}
EvidenceDecisiveOf == [frame \in {EvidenceClaimFrame} |-> EvidenceDecisive]
EvidenceController(mode, behavior) ==
    IF mode = "protocol" THEN "alk-protocol"
    ELSE IF behavior \in {"capture", "bind"} THEN "budget-authority"
    ELSE "recovery-provider"
EvidenceControls(mode) ==
    [frame \in {EvidenceClaimFrame} |->
        [principal \in Principals |->
            {behavior \in EvidenceDecisive :
                EvidenceController(mode, behavior) = principal}]]
EvidenceExcludes ==
    [frame \in {EvidenceClaimFrame} |-> [principal \in Principals |-> {}]]
EvidenceOwners(mode) ==
    {<<EvidenceClaimFrame, principal>> :
        principal \in ({"alk-protocol"} \cap
            EligibleOwners(EvidenceClaimFrame, Principals, EvidenceDecisiveOf,
                           EvidenceControls(mode), EvidenceExcludes))}

EvidenceInit ==
    /\ Init /\ Audit!Init
    /\ evidencePhase = "ready" /\ diagnosticTick = 0
    /\ alarmRaised = FALSE /\ stateRecovered = FALSE
    /\ snapshotRetained = TRUE
    /\ capturedBudget = budgetVars
    /\ recordFrame = BudgetFrame
    /\ recordSource = "budget-authority"
    /\ recordClaimant = "job-controller"
    /\ assertCurrentTruth = FALSE /\ observeCurrentTruth = FALSE

Capture ==
    /\ evidencePhase = "ready"
    /\ BudgetContract!TryAllocate(1)
    /\ UNCHANGED sequentialVars
    /\ Audit!Record(1)
    /\ capturedBudget' = budgetVars'
    /\ evidencePhase' = "captured"
    /\ UNCHANGED <<diagnosticTick, alarmRaised, stateRecovered, snapshotRetained,
                   recordFrame, recordSource, recordClaimant,
                   assertCurrentTruth, observeCurrentTruth>>

InjectPersistentOverallocation ==
    /\ evidencePhase = "captured"
    /\ budget_allocated' = budget_capacity + 1
    /\ diagnosticTick' = 1
    /\ evidencePhase' = "fault"
    /\ UNCHANGED <<budget_capacity, budget_reserved, budget_pending_eviction,
                   sequentialVars, evidenceLog, evidenceHash, capturedBudget,
                   alarmRaised, stateRecovered, snapshotRetained,
                   recordFrame, recordSource, recordClaimant,
                   assertCurrentTruth, observeCurrentTruth>>

MonitorTick(performRead) ==
    /\ evidencePhase = "fault" /\ diagnosticTick < 3
    /\ diagnosticTick' = diagnosticTick + 1
    /\ IF diagnosticTick' = 3
          THEN /\ alarmRaised' = (performRead /\ ~BudgetContract!SafetyInvariant)
               /\ evidencePhase' = "detected"
          ELSE /\ UNCHANGED alarmRaised /\ evidencePhase' = "fault"
    /\ UNCHANGED <<vars, evidenceLog, evidenceHash, capturedBudget, stateRecovered,
                   snapshotRetained, recordFrame, recordSource, recordClaimant,
                   assertCurrentTruth, observeCurrentTruth>>

RecoveryTick(copySnapshot) ==
    /\ evidencePhase = "detected" /\ diagnosticTick < 5
    /\ diagnosticTick' = diagnosticTick + 1
    /\ IF diagnosticTick' = 5
          THEN /\ snapshotRetained
               /\ budget_capacity' = capturedBudget[1]
               /\ budget_allocated' =
                    IF copySnapshot THEN capturedBudget[2] ELSE budget_allocated
               /\ budget_reserved' = capturedBudget[3]
               /\ budget_pending_eviction' = capturedBudget[4]
               /\ stateRecovered' = TRUE
               /\ evidencePhase' = "restored"
          ELSE /\ UNCHANGED budgetVars
               /\ UNCHANGED stateRecovered
               /\ evidencePhase' = "detected"
    /\ UNCHANGED <<sequentialVars, evidenceLog, evidenceHash, capturedBudget,
                   alarmRaised, snapshotRetained, recordFrame, recordSource,
                   recordClaimant, assertCurrentTruth, observeCurrentTruth>>

EvidenceDone == evidencePhase = "restored" /\ UNCHANGED evidenceVars
EvidenceNext ==
    Capture \/ InjectPersistentOverallocation \/ MonitorTick(TRUE)
      \/ RecoveryTick(TRUE) \/ EvidenceDone
EvidenceSpec ==
    /\ EvidenceInit /\ [][EvidenceNext]_evidenceVars
    /\ WF_evidenceVars(EvidenceNext)

RecordedObservationExists == Len(evidenceLog) = 1
RecordMetadataHeld ==
    RecordedObservationExists =>
        /\ recordFrame = BudgetFrame
        /\ recordSource = CanonicalOwner(BudgetFrame, Principals, DerivedOwnership("direct"))
        /\ recordClaimant = BudgetFrame.claimant
        /\ evidenceLog[1].operation = 1
CustodyHeld == RecordedObservationExists => snapshotRetained
CapturedObservationHeld ==
    RecordedObservationExists =>
        /\ CapturedContract!SafetyInvariant
        /\ capturedBudget = <<2, 1, 0, 0>>
DetectionBoundHeld ==
    diagnosticTick >= 3 => alarmRaised
RecoveryBoundHeld ==
    diagnosticTick >= 5 => stateRecovered
RecoveredSnapshotHeld ==
    stateRecovered =>
        /\ snapshotRetained
        /\ budgetVars = capturedBudget
        /\ BudgetContract!SafetyInvariant

\* A1 attribution does not make a statement true. A2 observation is about
\* the captured state at tick 0, not the later corrupted state.
AttributedAssertionLimitHeld ==
    assertCurrentTruth => BudgetContract!SafetyInvariant
PointObservationLimitHeld ==
    observeCurrentTruth => BudgetContract!SafetyInvariant

ActiveClasses ==
    {"A0"} \cup
    (IF RecordedObservationExists THEN {"A1", "A2", "A5"} ELSE {}) \cup
    (IF alarmRaised THEN {"A3"} ELSE {}) \cup
    (IF stateRecovered THEN {"A4"} ELSE {})

ClassFrame(class) ==
    CASE class = "A3" -> DetectionFrame
      [] class = "A4" -> RecoveryFrame
      [] OTHER -> BudgetFrame
ClassClaim(class) ==
    CASE class = "A0" -> "reliance-only"
      [] class = "A1" -> "source-attributed-assertion-only"
      [] class = "A2" -> "captured-budget-safe-at-tick-zero"
      [] class = "A3" -> "persistent-overallocation-observed-within-two-ticks"
      [] class = "A4" -> "snapshot-restored-within-four-ticks-one-tick-rpo"
      [] OTHER -> "budget-owner-guarantee-at-capture-only"
ClassEvidence(class) ==
    CASE class = "A0" -> {}
      [] class = "A3" -> {"independent-monitor-read-at-tick-three"}
      [] class = "A4" -> {"retained-snapshot-and-equal-restoration"}
      [] OTHER -> {"bound-observation-record"}
ClassRecords ==
    [class \in ActiveClasses |->
        [frame |-> ClassFrame(class), claimant |-> "job-controller",
         proposition |-> ClassClaim(class), evidence |-> ClassEvidence(class)]]

BehavioralClassCeilingsHeld ==
    /\ ActiveClasses \subseteq AssuranceClassNames
    /\ ClassRecords["A0"].evidence = {}
    /\ ("A2" \in ActiveClasses => CapturedObservationHeld)
    /\ ("A3" \in ActiveClasses => diagnosticTick >= 3)
    /\ ("A4" \in ActiveClasses => RecoveredSnapshotHeld)
    /\ ("A5" \in ActiveClasses =>
          /\ RecordMetadataHeld /\ CapturedObservationHeld)
    /\ AttributedAssertionLimitHeld /\ PointObservationLimitHeld

EvidenceTypeHeld ==
    /\ BudgetContract!TypeInvariant
    /\ SequentialContract!TypeInvariant
    /\ evidencePhase \in {"ready", "captured", "fault", "detected", "restored"}
    /\ diagnosticTick \in 0..5
    /\ alarmRaised \in BOOLEAN /\ stateRecovered \in BOOLEAN
    /\ snapshotRetained \in BOOLEAN
    /\ capturedBudget \in (Nat \X Nat \X Nat \X Nat)
    /\ recordFrame \in Frames
    /\ recordSource \in Principals /\ recordClaimant \in Principals
    /\ assertCurrentTruth \in BOOLEAN /\ observeCurrentTruth \in BOOLEAN
AuditContractHeld ==
    Audit!TypeInvariant /\ Audit!ChainIntegrity /\ Audit!HashConsistency /\ Audit!HashBindsContent
EvidenceAuthorityHeld ==
    /\ EvidenceOwners("protocol") = {<<EvidenceClaimFrame, "alk-protocol">>}
    /\ EvidenceOwners("split-custody") = {}

EvidenceInvariant ==
    /\ EvidenceTypeHeld /\ AuditContractHeld
    /\ RecordMetadataHeld /\ CustodyHeld /\ CapturedObservationHeld
    /\ DetectionBoundHeld /\ RecoveryBoundHeld /\ RecoveredSnapshotHeld
    /\ EvidenceAuthorityHeld /\ BehavioralClassCeilingsHeld

EventualRestoration == <>stateRecovered
====
