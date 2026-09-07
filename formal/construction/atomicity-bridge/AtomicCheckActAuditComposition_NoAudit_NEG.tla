---- MODULE AtomicCheckActAuditComposition_NoAudit_NEG ----
\* ====================================================================
\* NEGATIVE CONTROL (required to VIOLATE): the merged transition with
\* its AUDIT APPEND defused. The guard and the act are untouched and
\* still fused; what is removed is the record. This is the sharpest
\* form of separating the audit from the act -- the act happens and the
\* record does not -- and it is what AuditExact exists to catch: the
\* log length is no longer the consumed count.
\*
\* TLC must report AuditExact violated, at the first act. A CLEAN run
\* here would mean the exactness obligation is held by something other
\* than the append being in the same transition as the act, and the
\* fused step's emergent obligation would be carried by nothing.
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

\* THE DEFUSED MECHANISM: `log' = Append(log, i)` becomes UNCHANGED log.
\* The guard and the act are the namesake's verbatim and still fire in
\* ONE transition; only the record is gone.
Op(i) ==
    /\ i \notin Committed
    /\ x < Cap
    /\ x' = x + 1
    /\ UNCHANGED log

Next == \E i \in Invokers : Op(i)

Spec == Init /\ [][Next]_vars

Ceiling == x <= Cap

AuditExact == Len(log) = x

AuditUnique ==
    \A j, k \in DOMAIN log : log[j] = log[k] => j = k
====
