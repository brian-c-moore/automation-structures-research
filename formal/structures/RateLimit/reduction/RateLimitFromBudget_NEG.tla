---- MODULE RateLimitFromBudget_NEG ----
\* Refinement negative control. A fresh-window grant leaves window_start
\* unchanged instead of re-anchoring it to clock. BudgetSafety still holds, so
\* the refinement property must detect the mismatched rollover step.
EXTENDS Naturals

CONSTANTS Capacity, WindowDuration, MaxClock

VARIABLES capacity, allocated, reserved, pending_eviction, window_start, clock
vars == <<capacity, allocated, reserved, pending_eviction, window_start, clock>>

\* Budget component.
Budget == INSTANCE Budget WITH Capacity <- Capacity

TypeInvariant ==
    /\ capacity = Capacity
    /\ allocated \in 0..Capacity
    /\ reserved = 0
    /\ pending_eviction = 0
    /\ window_start \in Nat
    /\ clock \in Nat

BudgetSafety == Budget!SafetyInvariant

Init ==
    /\ capacity = Capacity
    /\ allocated = 0
    /\ reserved = 0
    /\ pending_eviction = 0
    /\ window_start = 0
    /\ clock = 0

AcquireWithinWindow ==
    /\ clock - window_start < WindowDuration
    /\ allocated < Capacity
    /\ allocated' = allocated + 1
    /\ UNCHANGED <<capacity, reserved, pending_eviction, window_start, clock>>

\* Fault: omit the fresh-window anchor update.
AcquireFreshWindow ==
    /\ clock - window_start >= WindowDuration
    /\ allocated' = 1
    /\ UNCHANGED <<capacity, reserved, pending_eviction, window_start, clock>>

AcquireDenied ==
    /\ clock - window_start < WindowDuration
    /\ allocated >= Capacity
    /\ UNCHANGED vars

Tick ==
    /\ clock < MaxClock
    /\ clock' = clock + 1
    /\ UNCHANGED <<capacity, allocated, reserved, pending_eviction, window_start>>

Next == AcquireWithinWindow \/ AcquireFreshWindow \/ AcquireDenied \/ Tick

Spec == Init /\ [][Next]_vars

RL == INSTANCE RateLimit WITH
        count <- allocated, window_start <- window_start, clock <- clock,
        MaxPerWindow <- Capacity, WindowDuration <- WindowDuration, MaxClock <- MaxClock

RLRefinement == RL!Spec

\* The configuration must report a violation of RLRefinement.
====
