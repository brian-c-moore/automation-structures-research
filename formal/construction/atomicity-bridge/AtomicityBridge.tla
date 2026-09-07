---- MODULE AtomicityBridge ----
\* Split implementation of AtomicCheckActAuditComposition. Check, act, and
\* audit are separate steps executed under one lock, with concurrent invokers
\* represented by independent program counters.
\*
\* The refinement linearizes at Act. MappedLog includes the single staged
\* record before Audit appends it, so Audit maps to a target stutter. The lock
\* keeps the check guard stable and permits at most one staged record. The
\* no-lock and audit-outside controls respectively break those two premises.
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Invokers,   \* finite set of invoker identities
          Cap,        \* the ceiling on the governed counter
          NoLock      \* the free-lock marker, not an invoker

ASSUME CapType == Cap \in Nat
ASSUME NoLockFresh == NoLock \notin Invokers

VARIABLES x,          \* governed state: consumed count
          log,        \* audit log: append-ordered invoker records
          lock,       \* NoLock, or the invoker holding the section
          pc          \* per-invoker program counter

vars == <<x, log, lock, pc>>

PCStates == {"idle", "has_lock", "checked", "acted", "audited",
             "aborted", "done"}

\* Program counters that mean "inside the critical section".
CSStates == {"has_lock", "checked", "acted", "aborted", "audited"}

\* Typing is separate from the Ceiling obligation. In particular, x \in Nat
\* excludes a decrementing implementation that would satisfy x <= Cap while
\* moving in the wrong direction.
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

\* Enter the critical section.
Acquire(i) ==
    /\ pc[i] = "idle"
    /\ lock = NoLock
    /\ lock' = i
    /\ pc' = [pc EXCEPT ![i] = "has_lock"]
    /\ UNCHANGED <<x, log>>

\* The check, as its own machine step, under the lock.
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

\* The act, as its own machine step, under the lock.
Act(i) ==
    /\ pc[i] = "checked"
    /\ lock = i
    /\ x' = x + 1
    /\ pc' = [pc EXCEPT ![i] = "acted"]
    /\ UNCHANGED <<log, lock>>

\* The audit append, in the SAME critical section as the act.
Audit(i) ==
    /\ pc[i] = "acted"
    /\ lock = i
    /\ log' = Append(log, i)
    /\ pc' = [pc EXCEPT ![i] = "audited"]
    /\ UNCHANGED <<x, lock>>

\* Leave the critical section -- only after the audit (or an abort).
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

\* ----- INVARIANTS -----
\*
\* Each invariant below has a paired control that removes the mechanism named
\* in its comment while leaving the declared obligation unchanged.

\* The lock discipline: the section is empty exactly when the lock is
\* free, and only the holder is inside.
\* Falsified by AtomicityBridge_NoMutex_NEG, which defuses mutual
\* exclusion at entry: a second invoker walks into an occupied section.
LockDiscipline ==
    IF lock = NoLock
    THEN \A i \in Invokers : pc[i] \notin CSStates
    ELSE /\ pc[lock] \in CSStates
         /\ \A i \in Invokers : i # lock => pc[i] \notin CSStates

\* TOCTOU-freedom: a passed check is still true at the act -- the
\* window between them admits no interfering act (the lock's work).
\* Falsified by AtomicityBridge_NoGuard_NEG, which defuses the ceiling
\* test inside the check step: the step is still taken under the lock
\* and tests nothing, so an invoker stands checked with the ceiling
\* already reached.
CheckedImpliesGuard ==
    \A i \in Invokers : pc[i] = "checked" => x < Cap

\* The obligation, at this layer's granularity.
\* Falsified by AtomicityBridge_UncheckedAct_NEG, which defuses the
\* act's dependence on a passed check: the section consumes without
\* having tested the ceiling, and the count runs past it.
Ceiling == x <= Cap

Staged == {i \in Invokers : pc[i] = "acted"}

\* Exactness at commit granularity: acts and records agree up to the
\* at-most-one staged record still inside its critical section.
\* Falsified by AtomicityBridge_NoAudit_NEG, which defuses the append:
\* the act happens inside the section and the record does not.
AuditSync == Len(log) + Cardinality(Staged) = x

\* ----- REFINEMENT: the critical section implements the fused step ---

\* Linearize at the act: a staged record counts as already appended.
MappedLog ==
    IF Staged = {} THEN log
    ELSE Append(log, CHOOSE i \in Staged : TRUE)

H == INSTANCE AtomicCheckActAuditComposition WITH x <- x, log <- MappedLog

\* Every behaviour of the lock-protected split realization is a
\* behaviour of the merged-transition composition spec.
Refinement == H!Spec

\* The paired configuration checks Refinement at finite bounds;
\* AtomicityBridge_Proof proves Spec => H!Spec parametrically.
====
