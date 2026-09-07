---- MODULE AtomicityBridge_NoLock_NEG ----
\* NEGATIVE CONTROL: remove the critical section from the split check, act,
\* and audit steps. Two invokers can pass the same check before either acts;
\* the second act then has no matching guarded target step. The paired
\* configuration must violate Refinement.
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Invokers, Cap

ASSUME CapType == Cap \in Nat

VARIABLES x, log, pc

vars == <<x, log, pc>>

PCStates == {"idle", "checked", "acted", "audited", "aborted", "done"}

\* Typing matches the carrier's non-lock state; Refinement is the configured
\* target rather than the derived ceiling violation.
TypeInvariant ==
    /\ x \in Nat
    /\ log \in Seq(Invokers)
    /\ pc \in [Invokers -> PCStates]

Init ==
    /\ x = 0
    /\ log = <<>>
    /\ pc = [i \in Invokers |-> "idle"]

\* The same steps as AtomicityBridge, minus every lock conjunct.
CheckPass(i) ==
    /\ pc[i] = "idle"
    /\ x < Cap
    /\ pc' = [pc EXCEPT ![i] = "checked"]
    /\ UNCHANGED <<x, log>>

CheckFail(i) ==
    /\ pc[i] = "idle"
    /\ x >= Cap
    /\ pc' = [pc EXCEPT ![i] = "aborted"]
    /\ UNCHANGED <<x, log>>

Act(i) ==
    /\ pc[i] = "checked"
    /\ x' = x + 1
    /\ pc' = [pc EXCEPT ![i] = "acted"]
    /\ UNCHANGED log

Audit(i) ==
    /\ pc[i] = "acted"
    /\ log' = Append(log, i)
    /\ pc' = [pc EXCEPT ![i] = "audited"]
    /\ UNCHANGED x

Finish(i) ==
    /\ pc[i] \in {"audited", "aborted"}
    /\ pc' = [pc EXCEPT ![i] = "done"]
    /\ UNCHANGED <<x, log>>

Next ==
    \E i \in Invokers :
        CheckPass(i) \/ CheckFail(i) \/ Act(i) \/ Audit(i) \/ Finish(i)

Spec == Init /\ [][Next]_vars

Staged == {i \in Invokers : pc[i] = "acted"}

MappedLog ==
    IF Staged = {} THEN log
    ELSE Append(log, CHOOSE i \in Staged : TRUE)

H == INSTANCE AtomicCheckActAuditComposition WITH x <- x, log <- MappedLog

Refinement == H!Spec
====
