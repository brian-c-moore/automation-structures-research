------------------- MODULE BridgeInitializationBroken_NEG -------------------
EXTENDS GovernedCommitExecutable

(* Fault: durable audit evidence is reported at initialization even though the
   executable AuditSink is empty. *)
BrokenInit ==
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
    /\ evidencePersisted = TRUE
    /\ recoveryIntent = FALSE
    /\ crashed = FALSE
    /\ lastClass = "init"

BrokenSpec == BrokenInit /\ [][Next]_vars

=============================================================================
