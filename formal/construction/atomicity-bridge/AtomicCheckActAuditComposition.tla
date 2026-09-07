---- MODULE AtomicCheckActAuditComposition ----
\* ====================================================================
\* The merged-transition semantics of a composition unit, stated
\* abstractly. This is the target of the atomicity bridge: the
\* specification a compliant critical section must implement -- one that
\* appends its audit record in the same section as the act it records.
\*
\* One invoker operation = guard check (ceiling) + state act (consume)
\* + audit append, fused into ONE transition. That is the check/act/
\* audit unit at the abstraction the composition catalog uses: the
\* governed state is the Counter-plus-ceiling shape and the log is the
\* Accumulator shape; their synchronization (AuditExact) is the
\* emergent obligation of the fused step, held by no component alone.
\* ====================================================================
EXTENDS Naturals, Sequences

CONSTANTS Invokers,   \* finite set of invoker identities
          Cap         \* the ceiling on the governed counter

ASSUME CapType == Cap \in Nat

VARIABLES x,          \* governed state: consumed count, ceiling Cap
          log         \* audit log: commit-ordered invoker records

vars == <<x, log>>

Committed == {log[k] : k \in DOMAIN log}

\* Typing only. The ceiling is an OBLIGATION, not a type: it is stated
\* once, as Ceiling below, and carried by the guard inside Op.
\* Held by construction like the three obligations below, and falsified
\* by AtomicCheckActAuditComposition_Decrement_NEG, which debits where the fused step
\* credits. That control is what establishes this invariant as
\* load-bearing rather than well-formedness: `x <= Cap` is satisfied
\* forever by a count running backwards, so without `x \in Nat` the
\* ceiling obligation holds over a step consuming without bound.
TypeInvariant ==
    /\ x \in Nat
    /\ log \in Seq(Invokers)

Init ==
    /\ x = 0
    /\ log = <<>>

\* The fused step: check, act, and audit commit atomically. Each
\* invoker operates at most once (one-shot discipline).
Op(i) ==
    /\ i \notin Committed
    /\ x < Cap
    /\ x' = x + 1
    /\ log' = Append(log, i)

Next == \E i \in Invokers : Op(i)

Spec == Init /\ [][Next]_vars

\* ----- INVARIANTS (the fused unit's obligations) -----
\*
\* All three below are HELD BY CONSTRUCTION of the fused step: Op is one
\* transition whose guard, act and append cannot be separated, so no
\* action in THIS module can falsify any of them. Each therefore carries
\* the paired adversary that supplies its falsification -- a sibling
\* module identical to this one but for the single mechanism it defuses,
\* required to violate and run by the canonical driver. The driver also
\* runs each pairing the other way, this module under the sibling's own
\* config, where it is required to stay clean: a violation is
\* attributable to the defused mechanism only once the model it was
\* found in has been shown sound against the unmutated module.

\* The ceiling holds -- the check is never outrun by the act.
\* Falsified by AtomicCheckActAuditComposition_NoCeiling_NEG, which defuses the
\* guard: the act is left ungoverned and the count runs past Cap.
Ceiling == x <= Cap

\* Exactness: every act carries exactly its audit record, in the same
\* transition -- the log length IS the consumed count.
\* Falsified by AtomicCheckActAuditComposition_NoAudit_NEG, which defuses the append:
\* the act happens and the record does not.
AuditExact == Len(log) = x

\* No invoker commits twice (exactly-once audit per operation).
\* Falsified by AtomicCheckActAuditComposition_NoOnceGuard_NEG, which defuses the
\* once-only condition: the read of the log that decides whether this
\* invoker has already committed is what makes the write exactly-once.
AuditUnique ==
    \A j, k \in DOMAIN log : log[j] = log[k] => j = k
====
