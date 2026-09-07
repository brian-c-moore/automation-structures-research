---- MODULE AtomicCheckActAuditComposition_Decrement_NEG ----
\* ====================================================================
\* NEGATIVE CONTROL (required to VIOLATE): the merged transition with
\* the DIRECTION OF THE ACT defused. The guard, the once-only condition
\* and the audit append are the namesake's, and all of it still fires in
\* ONE transition; what changes is the one term by which the fused step
\* moves the governed count -- it debits where the namesake credits. The
\* consumed count leaves the naturals on the first operation. TLC must
\* report TypeInvariant violated.
\*
\* WHY THIS OBLIGATION IS LOAD-BEARING RATHER THAN WELL-FORMEDNESS, and
\* it is the reason this control exists: the ceiling obligation is
\* `x <= Cap`, which a count running backwards satisfies forever. Strike
\* `x \in Nat` and a fused step that debits on every operation passes the
\* ceiling at every state while consuming without bound in the other
\* direction. The typing invariant is what stands between the governed
\* count and that reading, so a run in which nothing can falsify it is a
\* run in which the ceiling means less than it appears to. This is the
\* same defect and the same obligation as the one the split realization's
\* own debit control carries, stated at the merged scale -- the pair is
\* the bridge's own cross-scale correspondence applied to typing.
\*
\* The fused step, every obligation and the typing are the namesake's
\* CODE unchanged, but for the EXTENDS: Integers replaces Naturals,
\* because a module that cannot express the defect cannot be checked for
\* it. The declarations carry none of the namesake's per-line commentary,
\* which the mutation would falsify: the count here is no longer the
\* consumed count the namesake's declaration describes.
\*
\* At the state that first breaks typing this mutation also breaks
\* AuditExact, the record and the count having parted company. The
\* config declares TypeInvariant alone -- there is no second obligation
\* to declare beside it when typing is itself the obligation under test
\* -- and that is what makes the violation TLC reports attributable to
\* typing rather than collateral.
\* ====================================================================
EXTENDS Integers, Sequences

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

\* THE DEFUSED MECHANISM: `x' = x + 1` becomes `x' = x - 1`. The guard,
\* the once-only condition and the append are the namesake's verbatim,
\* and the step still moves the count by one -- in the direction that
\* leaves the naturals. Integers replaces Naturals in the EXTENDS above
\* for the same reason a mutation is written at all: a module that
\* cannot express the defect cannot be checked for it.
Op(i) ==
    /\ i \notin Committed
    /\ x < Cap
    /\ x' = x - 1
    /\ log' = Append(log, i)

Next == \E i \in Invokers : Op(i)

Spec == Init /\ [][Next]_vars

Ceiling == x <= Cap

AuditExact == Len(log) = x

AuditUnique ==
    \A j, k \in DOMAIN log : log[j] = log[k] => j = k
====
