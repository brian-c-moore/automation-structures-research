---- MODULE BisectionFromBudget_NEG ----
\* Negative control for the fused probe. ProbeLeft narrows the interval without
\* charging Budget. The carried invariants remain valid, but the step cannot
\* map to a target probe or stutter and must violate BRefinement.

EXTENDS Naturals

CONSTANTS DomainSize, Threshold, MaxProbes

VARIABLES lo, hi, b_capacity, b_allocated, b_reserved, b_pending

vars == <<lo, hi, b_capacity, b_allocated, b_reserved, b_pending>>

Bgt == INSTANCE Budget WITH Capacity <- MaxProbes,
                            capacity <- b_capacity,
                            allocated <- b_allocated,
                            reserved <- b_reserved,
                            pending_eviction <- b_pending

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

Mid == (lo + hi) \div 2

\* Fault: the Budget charge is omitted.
ProbeLeft ==
    /\ hi - lo >= 2
    /\ Mid >= Threshold
    /\ b_allocated + b_reserved + b_pending + 1 <= b_capacity
    /\ hi' = Mid
    /\ lo' = lo
    /\ UNCHANGED <<b_capacity, b_allocated, b_reserved, b_pending>>

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

Spec == Init /\ [][Next]_vars /\ WF_vars(ProbeLeft \/ ProbeRight)

B == INSTANCE Bisection WITH
        lo           <- lo,
        hi           <- hi,
        probes_taken <- b_allocated,
        DomainSize   <- DomainSize,
        Threshold    <- Threshold,
        MaxProbes    <- MaxProbes

BRefinement == B!Spec

\* The negative configuration must violate BRefinement.
====
