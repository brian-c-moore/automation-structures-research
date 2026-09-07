---- MODULE AtomicCheckActAuditComposition_NoCeiling_NEG ----
\* ====================================================================
\* NEGATIVE CONTROL (required to VIOLATE): the merged transition with
\* its GUARD defused. Op still acts and still appends in one step; what
\* is removed is the ceiling check `x < Cap` that the act is fused to.
\* With the guard gone the act is no longer governed by anything, so
\* the consumed count runs past the ceiling. TLC must report Ceiling
\* violated; a CLEAN run here would mean the target's ceiling
\* obligation is satisfied by something other than its own guard, and
\* the fused step would not be carrying it.
\*
\* Typing is the namesake's, exactly: `x \in Nat`. The namesake states
\* its ceiling once, as the Ceiling obligation, and this control's
\* config checks precisely that obligation -- so the breach this module
\* produces is reported as the Ceiling violation it is, and cannot
\* surface as a type violation instead.
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

\* THE DEFUSED MECHANISM: the guard `x < Cap` is gone. Everything else
\* -- the once-only condition, the act, the append -- is the namesake's
\* verbatim, and all of it still happens in ONE transition.
Op(i) ==
    /\ i \notin Committed
    /\ x' = x + 1
    /\ log' = Append(log, i)

Next == \E i \in Invokers : Op(i)

Spec == Init /\ [][Next]_vars

Ceiling == x <= Cap

AuditExact == Len(log) = x

AuditUnique ==
    \A j, k \in DOMAIN log : log[j] = log[k] => j = k
====
