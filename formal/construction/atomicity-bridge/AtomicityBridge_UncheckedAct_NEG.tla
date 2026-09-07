---- MODULE AtomicityBridge_UncheckedAct_NEG ----
\* NEGATIVE CONTROL: Act may run directly from has_lock as well as checked.
\* The lock and normal check path remain, but an invoker can consume without
\* testing the ceiling. The paired configuration must violate Ceiling.
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Invokers, Cap, NoLock

ASSUME CapType == Cap \in Nat
ASSUME NoLockFresh == NoLock \notin Invokers

VARIABLES x, log, lock, pc

vars == <<x, log, lock, pc>>

PCStates == {"idle", "has_lock", "checked", "acted", "audited",
             "aborted", "done"}

CSStates == {"has_lock", "checked", "acted", "aborted", "audited"}

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

\* MUTATION: widen the Act guard from checked to {has_lock, checked}.
Act(i) ==
    /\ pc[i] \in {"has_lock", "checked"}
    /\ lock = i
    /\ x' = x + 1
    /\ pc' = [pc EXCEPT ![i] = "acted"]
    /\ UNCHANGED <<log, lock>>

Audit(i) ==
    /\ pc[i] = "acted"
    /\ lock = i
    /\ log' = Append(log, i)
    /\ pc' = [pc EXCEPT ![i] = "audited"]
    /\ UNCHANGED <<x, lock>>

Release(i) ==
    /\ pc[i] \in {"audited", "aborted"}
    /\ lock = i
    /\ lock' = NoLock
    /\ pc' = [pc EXCEPT ![i] = "done"]
    /\ UNCHANGED <<x, log>>

Next ==
    \E i \in Invokers :
        Acquire(i) \/ CheckPass(i) \/ CheckFail(i)
        \/ Act(i) \/ Audit(i) \/ Release(i)

Spec == Init /\ [][Next]_vars

LockDiscipline ==
    IF lock = NoLock
    THEN \A i \in Invokers : pc[i] \notin CSStates
    ELSE /\ pc[lock] \in CSStates
         /\ \A i \in Invokers : i # lock => pc[i] \notin CSStates

CheckedImpliesGuard ==
    \A i \in Invokers : pc[i] = "checked" => x < Cap

Ceiling == x <= Cap

Staged == {i \in Invokers : pc[i] = "acted"}

AuditSync == Len(log) + Cardinality(Staged) = x
====
