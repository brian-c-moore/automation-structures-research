---- MODULE BisectionFromBudget ----
\* Construction of Bisection from Budget<Probes> and G v1.1. Budget allocation
\* represents probes_taken; lo and hi are CF-002 Cursor state; Mid is a CF-001
\* Projection; the Threshold comparison is domain-supplied predicate content.
\* Each probe narrows the correct side and charges Budget in one atomic
\* transition. DomainFitsProbes ensures the Budget guard does not disable a
\* live probe, so the target weak-fairness condition transfers.

EXTENDS Naturals

CONSTANTS DomainSize, Threshold, MaxProbes

\* Budget component state (b_*) + the converging cursor pair (lo, hi).
VARIABLES lo, hi, b_capacity, b_allocated, b_reserved, b_pending

vars == <<lo, hi, b_capacity, b_allocated, b_reserved, b_pending>>

Bgt == INSTANCE Budget WITH Capacity <- MaxProbes,
                            capacity <- b_capacity,
                            allocated <- b_allocated,
                            reserved <- b_reserved,
                            pending_eviction <- b_pending

\* Budget's allocation safety invariant over the probe counter.
BudgetSafety == Bgt!SafetyInvariant

TypeInvariant ==
    /\ lo \in 0..DomainSize
    /\ hi \in 0..DomainSize
    /\ b_capacity = MaxProbes
    /\ b_allocated \in 0..MaxProbes
    /\ b_reserved = 0
    /\ b_pending = 0

Init ==
    /\ lo \in 0..Threshold
    /\ hi \in Threshold..DomainSize
    /\ b_capacity = MaxProbes
    /\ b_allocated = 0
    /\ b_reserved = 0
    /\ b_pending = 0

\* The split-point Projection.
Mid == (lo + hi) \div 2

\* The fused probe: Bgt!TryAllocate(1)'s success branch + the correct-side
\* cursor narrowing, committed atomically. Two cases on the monotone
\* predicate at the midpoint (the domain content).
ProbeLeft ==
    /\ hi - lo >= 2
    /\ Mid >= Threshold
    /\ b_allocated + b_reserved + b_pending + 1 <= b_capacity
    /\ hi' = Mid
    /\ lo' = lo
    /\ b_allocated' = b_allocated + 1
    /\ UNCHANGED <<b_capacity, b_reserved, b_pending>>

ProbeRight ==
    /\ hi - lo >= 2
    /\ Mid < Threshold
    /\ b_allocated + b_reserved + b_pending + 1 <= b_capacity
    /\ lo' = Mid + 1
    /\ hi' = hi
    /\ b_allocated' = b_allocated + 1
    /\ UNCHANGED <<b_capacity, b_reserved, b_pending>>

Converged ==
    /\ hi - lo < 2
    /\ UNCHANGED vars

Next ==
    \/ ProbeLeft
    \/ ProbeRight
    \/ Converged

\* WF on the probes, mirroring the target's fairness so the liveness
\* conjunct of Bisection!Spec transfers.
Spec == Init /\ [][Next]_vars /\ WF_vars(ProbeLeft \/ ProbeRight)

\* --- Refinement mapping to Bisection ---
\* probes_taken is the Budget allocation; lo/hi map identically.
B == INSTANCE Bisection WITH
        lo           <- lo,
        hi           <- hi,
        probes_taken <- b_allocated,
        DomainSize   <- DomainSize,
        Threshold    <- Threshold,
        MaxProbes    <- MaxProbes

\* Every construction behavior, including the weak-fairness condition, maps
\* to a Bisection behavior.
BRefinement == B!Spec

\* BisectionFromBudget_Proof proves Spec => BRefinement under the domain and
\* probe-budget premises.
====
