----------------- MODULE BridgeStepPreservationBroken_NEG -----------------
EXTENDS GovernedCommitExecutable

(* Fault: propagation skips the Sequential carrier's ready boundary. *)
BadPropagate ==
    /\ phase = "Admitted"
    /\ ~crashed
    /\ propagationIteration = 0
    /\ phase' = "Ready"
    /\ propagationIteration' = 1
    /\ pc' = 3
    /\ lastClass' = "system"
    /\ UNCHANGED <<capacity, reserved, allocated, registryMapped,
                    actuationEffect, auditLen, attempts, maxAttempts,
                    effectApplied, evidencePersisted, recoveryIntent, crashed>>

MutantNext ==
    \/ AdmitAccepted
    \/ AdmitRejected
    \/ BadPropagate
    \/ FailBeforeEffect
    \/ FailAfterEffect
    \/ CommitSuccess
    \/ Recover
    \/ Crash
    \/ Restart

MutantSpec == Init /\ [][MutantNext]_vars

=============================================================================
