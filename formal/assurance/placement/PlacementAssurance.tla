---- MODULE PlacementAssurance ----
EXTENDS Naturals, TLC

CONSTANTS Direct, Delegated,
          NoAssurance, PreCommit, AtCommit, PostCommit,
          Prevention, Detection, Recovery, Lost,
          NoFault, PostAsPrevention, IgnorePartition,
          FaultMode

ASSUME Direct /= Delegated
ASSUME NoAssurance /= PreCommit /\ PreCommit /= AtCommit /\ AtCommit /= PostCommit
ASSUME NoAssurance /= AtCommit /\ NoAssurance /= PostCommit /\ PreCommit /= PostCommit
ASSUME Prevention /= Detection /\ Detection /= Recovery /\ Recovery /= Lost
ASSUME Prevention /= Recovery /\ Prevention /= Lost /\ Detection /= Lost
ASSUME FaultMode \in {NoFault, PostAsPrevention, IgnorePartition}

Placements == {Direct, Delegated}
Timings == {NoAssurance, PreCommit, AtCommit, PostCommit}
Kinds == {Prevention, Detection, Recovery, Lost}

VARIABLES phase,
          placement,
          timing,
          assuranceHealthy,
          partitioned,
          recoveryCapable,
          proposalViolates,
          committed,
          violation,
          evidence,
          restored,
          blocked

vars == <<phase, placement, timing, assuranceHealthy, partitioned,
          recoveryCapable, proposalViolates, committed, violation,
          evidence, restored, blocked>>

Reachable == ~partitioned

\* The delegated precommit and at-commit cases model a controller that can
\* block the same falsifying commit. A receipt or monitor outside that path
\* supplies assurance and does not satisfy ActualPrevents.
ActualPrevents ==
    placement = Direct
    \/ /\ placement = Delegated
       /\ timing \in {PreCommit, AtCommit}
       /\ assuranceHealthy
       /\ Reachable

ClassifiedPrevents ==
    ActualPrevents
    \/ /\ FaultMode = PostAsPrevention
       /\ placement = Delegated
       /\ timing = PostCommit
       /\ assuranceHealthy
       /\ Reachable
    \/ /\ FaultMode = IgnorePartition
       /\ placement = Delegated
       /\ timing \in {PreCommit, AtCommit}
       /\ assuranceHealthy

EffectiveKind ==
    IF ClassifiedPrevents THEN Prevention
    ELSE IF /\ placement = Delegated
            /\ timing = PostCommit
            /\ assuranceHealthy
            /\ Reachable
            /\ recoveryCapable
         THEN Recovery
    ELSE IF /\ placement = Delegated
            /\ timing = PostCommit
            /\ assuranceHealthy
            /\ Reachable
         THEN Detection
    ELSE Lost

Init ==
    /\ phase = "Ready"
    /\ placement \in Placements
    /\ timing \in Timings
    /\ assuranceHealthy \in BOOLEAN
    /\ partitioned \in BOOLEAN
    /\ recoveryCapable \in BOOLEAN
    /\ proposalViolates \in BOOLEAN
    /\ committed = FALSE
    /\ violation = FALSE
    /\ evidence = FALSE
    /\ restored = FALSE
    /\ blocked = FALSE

Commit ==
    /\ phase = "Ready"
    /\ IF ActualPrevents /\ proposalViolates
          THEN /\ phase' = "Done"
               /\ blocked' = TRUE
               /\ committed' = FALSE
               /\ violation' = FALSE
               /\ evidence' = assuranceHealthy /\ Reachable
               /\ restored' = FALSE
          ELSE /\ committed' = TRUE
               /\ violation' = proposalViolates
               /\ blocked' = FALSE
               /\ restored' = FALSE
               /\ IF placement = Direct
                     \/ /\ placement = Delegated
                        /\ timing \in {PreCommit, AtCommit}
                        /\ assuranceHealthy
                        /\ Reachable
                     THEN /\ phase' = "Done"
                          /\ evidence' = TRUE
                     ELSE /\ phase' = "Committed"
                          /\ evidence' = FALSE
    /\ UNCHANGED <<placement, timing, assuranceHealthy, partitioned,
                   recoveryCapable, proposalViolates>>

PostAssure ==
    /\ phase = "Committed"
    /\ placement = Delegated
    /\ timing = PostCommit
    /\ assuranceHealthy
    /\ Reachable
    /\ phase' = "Done"
    /\ evidence' = TRUE
    /\ restored' = violation /\ recoveryCapable
    /\ UNCHANGED <<placement, timing, assuranceHealthy, partitioned,
                   recoveryCapable, proposalViolates, committed,
                   violation, blocked>>

LoseAssurance ==
    /\ phase = "Committed"
    /\ ~(/\ placement = Delegated
          /\ timing = PostCommit
          /\ assuranceHealthy
          /\ Reachable)
    /\ phase' = "Done"
    /\ evidence' = FALSE
    /\ restored' = FALSE
    /\ UNCHANGED <<placement, timing, assuranceHealthy, partitioned,
                   recoveryCapable, proposalViolates, committed,
                   violation, blocked>>

Done ==
    /\ phase = "Done"
    /\ UNCHANGED vars

Next == Commit \/ PostAssure \/ LoseAssurance \/ Done
Spec == Init /\ [][Next]_vars

TypeInvariant ==
    /\ phase \in {"Ready", "Committed", "Done"}
    /\ placement \in Placements
    /\ timing \in Timings
    /\ assuranceHealthy \in BOOLEAN
    /\ partitioned \in BOOLEAN
    /\ recoveryCapable \in BOOLEAN
    /\ proposalViolates \in BOOLEAN
    /\ committed \in BOOLEAN
    /\ violation \in BOOLEAN
    /\ evidence \in BOOLEAN
    /\ restored \in BOOLEAN
    /\ blocked \in BOOLEAN
    /\ EffectiveKind \in Kinds

PreventionSound ==
    (phase = "Done" /\ EffectiveKind = Prevention) => ~violation

DetectionSound ==
    (phase = "Done" /\ EffectiveKind = Detection /\ violation) => evidence

RecoverySound ==
    (phase = "Done" /\ EffectiveKind = Recovery /\ violation) => (evidence /\ restored)

DirectBlocking ==
    (phase = "Done" /\ placement = Direct /\ proposalViolates) => (blocked /\ ~committed)

FailureCeiling ==
    (phase = "Done" /\ EffectiveKind = Lost /\ proposalViolates /\ ~blocked)
    => (violation /\ ~restored)

====
