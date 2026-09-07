--------------------- MODULE GovernedCommitExecutable ---------------------
EXTENDS Naturals, Integers, TLC, GovernedCommitAbstract

(* Generated semantic projection of the verified Rust API.  The translation
   checker binds every action below to the exact Rust method-contract body. *)

VARIABLES phase, capacity, reserved, allocated, registryMapped,
          propagationIteration, actuationEffect, auditLen, pc,
          attempts, maxAttempts, effectApplied, evidencePersisted,
          recoveryIntent, crashed, lastClass

vars == <<phase, capacity, reserved, allocated, registryMapped,
          propagationIteration, actuationEffect, auditLen, pc,
          attempts, maxAttempts, effectApplied, evidencePersisted,
          recoveryIntent, crashed, lastClass>>

ConcretePhases ==
    {"Pending", "Admitted", "Ready", "Retryable",
     "RecoveryPending", "Committed", "Rejected"}

Init ==
    /\ phase = "Pending"
    /\ capacity \in 0..1
    /\ reserved = 0
    /\ allocated = 0
    /\ registryMapped = TRUE
    /\ propagationIteration = 0
    /\ actuationEffect = FALSE
    /\ auditLen = 0
    /\ pc = 0
    /\ attempts = 0
    /\ maxAttempts \in 1..2
    /\ effectApplied = FALSE
    /\ evidencePersisted = FALSE
    /\ recoveryIntent = FALSE
    /\ crashed = FALSE
    /\ lastClass = "init"

AdmitAccepted ==
    /\ phase = "Pending"
    /\ ~crashed
    /\ capacity >= 1
    /\ phase' = "Admitted"
    /\ reserved' = 1
    /\ pc' = 1
    /\ lastClass' = "system"
    /\ UNCHANGED <<capacity, allocated, registryMapped,
                    propagationIteration, actuationEffect, auditLen,
                    attempts, maxAttempts, effectApplied, evidencePersisted,
                    recoveryIntent, crashed>>

AdmitRejected ==
    /\ phase = "Pending"
    /\ ~crashed
    /\ capacity = 0
    /\ phase' = "Rejected"
    /\ lastClass' = "failure"
    /\ UNCHANGED <<capacity, reserved, allocated, registryMapped,
                    propagationIteration, actuationEffect, auditLen, pc,
                    attempts, maxAttempts, effectApplied, evidencePersisted,
                    recoveryIntent, crashed>>

Propagate ==
    /\ phase = "Admitted"
    /\ ~crashed
    /\ propagationIteration = 0
    /\ phase' = "Ready"
    /\ propagationIteration' = 1
    /\ pc' = 2
    /\ lastClass' = "system"
    /\ UNCHANGED <<capacity, reserved, allocated, registryMapped,
                    actuationEffect, auditLen, attempts, maxAttempts,
                    effectApplied, evidencePersisted, recoveryIntent, crashed>>

FailBeforeEffect ==
    /\ phase \in {"Ready", "Retryable"}
    /\ ~crashed
    /\ attempts < maxAttempts
    /\ attempts' = attempts + 1
    /\ phase' = IF attempts' = maxAttempts THEN "Rejected" ELSE "Retryable"
    /\ lastClass' = "failure"
    /\ UNCHANGED <<capacity, reserved, allocated, registryMapped,
                    propagationIteration, actuationEffect, auditLen, pc,
                    maxAttempts, effectApplied, evidencePersisted,
                    recoveryIntent, crashed>>

FailAfterEffect ==
    /\ phase \in {"Ready", "Retryable"}
    /\ ~crashed
    /\ attempts < maxAttempts
    /\ ~effectApplied
    /\ ~evidencePersisted
    /\ ~recoveryIntent
    /\ attempts' = attempts + 1
    /\ phase' = "RecoveryPending"
    /\ actuationEffect' = TRUE
    /\ effectApplied' = TRUE
    /\ recoveryIntent' = TRUE
    /\ lastClass' = "failure"
    /\ UNCHANGED <<capacity, reserved, allocated, registryMapped,
                    propagationIteration, auditLen, pc, maxAttempts,
                    evidencePersisted, crashed>>

CommitSuccess ==
    /\ phase \in {"Ready", "Retryable"}
    /\ ~crashed
    /\ attempts < maxAttempts
    /\ reserved = 1
    /\ ~effectApplied
    /\ ~evidencePersisted
    /\ ~recoveryIntent
    /\ attempts' = attempts + 1
    /\ phase' = "Committed"
    /\ reserved' = 0
    /\ allocated' = 1
    /\ actuationEffect' = TRUE
    /\ auditLen' = 1
    /\ pc' = 3
    /\ effectApplied' = TRUE
    /\ evidencePersisted' = TRUE
    /\ recoveryIntent' = FALSE
    /\ lastClass' = "commit"
    /\ UNCHANGED <<capacity, registryMapped, propagationIteration,
                    maxAttempts, crashed>>

Recover ==
    /\ phase = "RecoveryPending"
    /\ ~crashed
    /\ reserved = 1
    /\ phase' = "Committed"
    /\ reserved' = 0
    /\ allocated' = 1
    /\ auditLen' = 1
    /\ pc' = 3
    /\ evidencePersisted' = TRUE
    /\ recoveryIntent' = FALSE
    /\ lastClass' = "commit"
    /\ UNCHANGED <<capacity, registryMapped, propagationIteration,
                    actuationEffect, attempts, maxAttempts, effectApplied,
                    crashed>>

Crash ==
    /\ ~crashed
    /\ crashed' = TRUE
    /\ lastClass' = "failure"
    /\ UNCHANGED <<phase, capacity, reserved, allocated, registryMapped,
                    propagationIteration, actuationEffect, auditLen, pc,
                    attempts, maxAttempts, effectApplied, evidencePersisted,
                    recoveryIntent>>

Restart ==
    /\ crashed
    /\ crashed' = FALSE
    /\ lastClass' = "stutter"
    /\ UNCHANGED <<phase, capacity, reserved, allocated, registryMapped,
                    propagationIteration, actuationEffect, auditLen, pc,
                    attempts, maxAttempts, effectApplied, evidencePersisted,
                    recoveryIntent>>

CommitActions == CommitSuccess \/ Recover
FailureActions == AdmitRejected \/ FailBeforeEffect \/ FailAfterEffect \/ Crash

Next ==
    \/ AdmitAccepted
    \/ AdmitRejected
    \/ Propagate
    \/ FailBeforeEffect
    \/ FailAfterEffect
    \/ CommitSuccess
    \/ Recover
    \/ Crash
    \/ Restart

SchedulerRely ==
    /\ SF_vars(AdmitAccepted \/ AdmitRejected)
    /\ SF_vars(Propagate)
    /\ SF_vars(CommitSuccess)
    /\ SF_vars(Recover)
    /\ SF_vars(Restart)

Spec == Init /\ [][Next]_vars /\ SchedulerRely

BasicTypeInvariant ==
    /\ phase \in ConcretePhases
    /\ capacity \in Nat
    /\ reserved \in Nat
    /\ allocated \in Nat
    /\ reserved + allocated <= capacity
    /\ registryMapped \in BOOLEAN
    /\ propagationIteration \in Nat
    /\ propagationIteration <= 1
    /\ actuationEffect \in BOOLEAN
    /\ auditLen \in Nat
    /\ auditLen <= 1
    /\ pc \in Nat
    /\ pc <= 3
    /\ attempts \in Nat
    /\ maxAttempts \in Nat
    /\ maxAttempts > 0
    /\ attempts <= maxAttempts
    /\ effectApplied \in BOOLEAN
    /\ evidencePersisted \in BOOLEAN
    /\ recoveryIntent \in BOOLEAN
    /\ crashed \in BOOLEAN
    /\ lastClass \in ActionClasses

RepresentationCoupling ==
    /\ registryMapped = TRUE
    /\ effectApplied = actuationEffect
    /\ evidencePersisted = (auditLen = 1)

PhaseCoupling ==
    /\ (phase = "Pending" => pc = 0)
    /\ (phase = "Pending"
        => allocated = 0 /\ reserved = 0 /\ ~effectApplied
           /\ ~evidencePersisted /\ ~recoveryIntent)
    /\ (phase = "Admitted" => pc = 1)
    /\ (phase \in {"Ready", "Retryable", "RecoveryPending"} => pc = 2)
    /\ (phase = "Committed" => pc = 3)
    /\ (phase \in {"Admitted", "Ready", "Retryable", "RecoveryPending"}
        => reserved = 1)
    /\ (phase \in {"Admitted", "Ready", "Retryable"}
        => allocated = 0 /\ ~effectApplied /\ ~evidencePersisted
           /\ ~recoveryIntent)
    /\ (phase = "Rejected"
        => ~effectApplied /\ ~evidencePersisted /\ ~recoveryIntent)
    /\ (phase = "RecoveryPending"
        => allocated = 0 /\ effectApplied /\ recoveryIntent /\ ~evidencePersisted)
    /\ (phase = "Committed"
        => effectApplied /\ evidencePersisted /\ ~recoveryIntent
           /\ allocated = 1 /\ reserved = 0)

TypeInvariant ==
    /\ BasicTypeInvariant
    /\ RepresentationCoupling
    /\ PhaseCoupling

CommitEvidenceCoupled == phase = "Committed" => evidencePersisted
CapacitySafe == allocated + reserved <= capacity
BridgeInvariant == TypeInvariant /\ CommitEvidenceCoupled /\ CapacitySafe

AbsPhase(p) ==
    IF p = "Pending" THEN "pending"
    ELSE IF p \in {"Admitted", "Ready", "Retryable"} THEN "active"
    ELSE IF p = "RecoveryPending" THEN "recovering"
    ELSE IF p = "Committed" THEN "committed"
    ELSE "failed"

AbsState ==
    [phase     |-> AbsPhase(phase),
     capacity  |-> capacity,
     used      |-> allocated + reserved,
     effect    |-> effectApplied,
     audited   |-> evidencePersisted,
     recovery  |-> recoveryIntent,
     lastClass |-> lastClass]

ConcreteObservation ==
    [externalEffect |-> effectApplied,
     committed     |-> phase = "Committed",
     audited       |-> evidencePersisted,
     failed        |-> AbsPhase(phase) \in {"failed", "recovering"}]

InitializationRelated == AbstractInit(AbsState)
StepPreservation == TypeInvariant
TransferredGuarantee == CapacitySafe /\ CommitEvidenceCoupled
EventualResolution == <> (phase \in {"Committed", "Rejected"})

=============================================================================
