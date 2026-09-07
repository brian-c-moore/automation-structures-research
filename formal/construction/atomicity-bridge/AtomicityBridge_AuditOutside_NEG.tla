---- MODULE AtomicityBridge_AuditOutside_NEG ----
\* NEGATIVE CONTROL: check and act retain the lock, but Release may occur
\* before AuditDeferred appends the record. A second invoker can then commit
\* first, making commit order and record order diverge. The paired
\* configuration must violate Refinement.
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Invokers, Cap, NoLock

ASSUME CapType == Cap \in Nat
ASSUME NoLockFresh == NoLock \notin Invokers

VARIABLES x, log, lock, pc

vars == <<x, log, lock, pc>>

PCStates == {"idle", "has_lock", "checked", "acted", "audited",
             "aborted", "done"}

\* Match the carrier's typing. Ceiling is intentionally not declared by the
\* control configuration because Refinement is the target obligation.
TypeInvariant ==
    /\ x \in Nat
    /\ log \in Seq(Invokers)
    /\ lock \in Invokers \cup {NoLock}
    /\ pc \in [Invokers -> PCStates]

Init ==
    /\ x = 0
    /\ log = <<>>
    /\ lock = NoLock
    /\ pc = [i \in Invokers |-> "idle"]

Acquire(i) ==
    /\ pc[i] = "idle"
    /\ lock = NoLock
    /\ lock' = i
    /\ pc' = [pc EXCEPT ![i] = "has_lock"]
    /\ UNCHANGED <<x, log>>

CheckPass(i) ==
    /\ pc[i] = "has_lock"
    /\ lock = i
    /\ x < Cap
    /\ pc' = [pc EXCEPT ![i] = "checked"]
    /\ UNCHANGED <<x, log, lock>>

CheckFail(i) ==
    /\ pc[i] = "has_lock"
    /\ lock = i
    /\ x >= Cap
    /\ pc' = [pc EXCEPT ![i] = "aborted"]
    /\ UNCHANGED <<x, log, lock>>

Act(i) ==
    /\ pc[i] = "checked"
    /\ lock = i
    /\ x' = x + 1
    /\ pc' = [pc EXCEPT ![i] = "acted"]
    /\ UNCHANGED <<log, lock>>

\* MUTATION: audit no longer requires the lock.
AuditDeferred(i) ==
    /\ pc[i] = "acted"
    /\ log' = Append(log, i)
    /\ pc' = [pc EXCEPT ![i] = "audited"]
    /\ UNCHANGED <<x, lock>>

\* MUTATION: Release is allowed with the audit pending.
Release(i) ==
    /\ pc[i] \in {"acted", "audited", "aborted"}
    /\ lock = i
    /\ lock' = NoLock
    /\ IF pc[i] = "acted"
       THEN pc' = pc            \* leaves the section still un-audited
       ELSE pc' = [pc EXCEPT ![i] = "done"]
    /\ UNCHANGED <<x, log>>

Next ==
    \E i \in Invokers :
        Acquire(i) \/ CheckPass(i) \/ CheckFail(i)
        \/ Act(i) \/ AuditDeferred(i) \/ Release(i)

Spec == Init /\ [][Next]_vars

Staged == {i \in Invokers : pc[i] = "acted"}

MappedLog ==
    IF Staged = {} THEN log
    ELSE Append(log, CHOOSE i \in Staged : TRUE)

H == INSTANCE AtomicCheckActAuditComposition WITH x <- x, log <- MappedLog

Refinement == H!Spec
====
