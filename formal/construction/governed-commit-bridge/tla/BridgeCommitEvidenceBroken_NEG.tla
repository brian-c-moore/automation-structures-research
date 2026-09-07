------------------ MODULE BridgeCommitEvidenceBroken_NEG ------------------
EXTENDS GovernedCommitExecutable

(* Fault: the external effect and budget commit become visible without the
   AuditSink append or durable evidence bit. *)
BadCommitSuccess ==
    /\ phase \in {"Ready", "Retryable"}
    /\ ~crashed
    /\ attempts < maxAttempts
    /\ reserved = 1
    /\ attempts' = attempts + 1
    /\ phase' = "Committed"
    /\ reserved' = 0
    /\ allocated' = 1
    /\ actuationEffect' = TRUE
    /\ auditLen' = 0
    /\ pc' = 3
    /\ effectApplied' = TRUE
    /\ evidencePersisted' = FALSE
    /\ recoveryIntent' = FALSE
    /\ lastClass' = "commit"
    /\ UNCHANGED <<capacity, registryMapped, propagationIteration,
                    maxAttempts, crashed>>

MutantNext ==
    \/ AdmitAccepted
    \/ AdmitRejected
    \/ Propagate
    \/ FailBeforeEffect
    \/ FailAfterEffect
    \/ BadCommitSuccess
    \/ Recover
    \/ Crash
    \/ Restart

MutantSpec == Init /\ [][MutantNext]_vars

=============================================================================
