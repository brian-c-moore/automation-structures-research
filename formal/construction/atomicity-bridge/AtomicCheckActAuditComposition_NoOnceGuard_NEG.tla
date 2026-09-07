---- MODULE AtomicCheckActAuditComposition_NoOnceGuard_NEG ----
\* ====================================================================
\* NEGATIVE CONTROL (required to VIOLATE): the merged transition with
\* its ONCE-ONLY condition defused. The guard, the act and the append
\* are untouched and still fused; what is removed is `i \notin
\* Committed`, the condition that reads the log to decide whether this
\* invoker has already committed. With it gone, one invoker commits
\* twice and appears in the log twice.
\*
\* TLC must report AuditUnique violated. A CLEAN run here would mean
\* exactly-once is held by something other than the operation
\* consulting its own record before acting -- which is the point the
\* target makes: the read of the log and the write to it are one step.
\* ====================================================================
EXTENDS Naturals, Sequences

CONSTANTS Invokers, Cap

ASSUME CapType == Cap \in Nat

VARIABLES x, log

vars == <<x, log>>

Committed == {log[k] : k \in DOMAIN log}

TypeInvariant ==
    /\ x \in Nat
    /\ log \in Seq(Invokers)

Init ==
    /\ x = 0
    /\ log = <<>>

\* THE DEFUSED MECHANISM: the conjunct `i \notin Committed` is gone.
\* The ceiling guard, the act and the append are the namesake's
\* verbatim and still fire in ONE transition.
Op(i) ==
    /\ x < Cap
    /\ x' = x + 1
    /\ log' = Append(log, i)

Next == \E i \in Invokers : Op(i)

Spec == Init /\ [][Next]_vars

Ceiling == x <= Cap

AuditExact == Len(log) = x

AuditUnique ==
    \A j, k \in DOMAIN log : log[j] = log[k] => j = k
====
