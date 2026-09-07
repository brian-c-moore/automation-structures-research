---- MODULE RateLimitFromBudget ----
\* RateLimit represented by a Budget allocation counter plus window_start and
\* a runtime-provided clock. A rollover atomically resets the allocation and
\* grants the triggering request. Budget supplies the count ceiling; the clock
\* and atomic rollover boundary are environment/implementation relies.

EXTENDS Naturals

CONSTANTS Capacity,        \* plays the role of RateLimit!MaxPerWindow
          WindowDuration,
          MaxClock

\* Budget component state (capacity/allocated/reserved/pending_eviction) plus
\* the windowing glue (window_start) and the runtime clock.
VARIABLES capacity, allocated, reserved, pending_eviction, window_start, clock

vars == <<capacity, allocated, reserved, pending_eviction, window_start, clock>>

\* Budget component and its carried safety predicate.
Budget == INSTANCE Budget WITH Capacity <- Capacity

BudgetSafety == Budget!SafetyInvariant   \* allocated+reserved+pending_eviction <= capacity

TypeInvariant ==
    /\ capacity = Capacity
    /\ allocated \in 0..Capacity
    /\ reserved = 0
    /\ pending_eviction = 0
    /\ window_start \in Nat
    /\ clock \in Nat

Init ==
    /\ capacity = Capacity
    /\ allocated = 0
    /\ reserved = 0
    /\ pending_eviction = 0
    /\ window_start = 0
    /\ clock = 0

\* Window still open, budget available: a plain Budget try_allocate(1).
\* Maps to RateLimit!TryAcquire, within-window branch (count < MaxPerWindow).
AcquireWithinWindow ==
    /\ clock - window_start < WindowDuration
    /\ allocated < Capacity
    /\ allocated' = allocated + 1
    /\ UNCHANGED <<capacity, reserved, pending_eviction, window_start, clock>>

\* Window expired: reset the Budget to empty (Release all) and allocate one in
\* the new window, committed atomically (assumption 2). Maps to
\* RateLimit!TryAcquire, fresh-window branch (window_start' = clock, count' = 1).
AcquireFreshWindow ==
    /\ clock - window_start >= WindowDuration
    /\ allocated' = 1
    /\ window_start' = clock
    /\ UNCHANGED <<capacity, reserved, pending_eviction, clock>>

\* Window open but budget exhausted: try_allocate fails -> stutter.
\* Maps to RateLimit!TryAcquire else-branch (UNCHANGED).
AcquireDenied ==
    /\ clock - window_start < WindowDuration
    /\ allocated >= Capacity
    /\ UNCHANGED vars

\* Runtime-provided clock action, identical to RateLimit!Tick.
Tick ==
    /\ clock < MaxClock
    /\ clock' = clock + 1
    /\ UNCHANGED <<capacity, allocated, reserved, pending_eviction, window_start>>

Next ==
    \/ AcquireWithinWindow
    \/ AcquireFreshWindow
    \/ AcquireDenied
    \/ Tick

Spec == Init /\ [][Next]_vars

\* Refinement mapping: the window count is the Budget allocation.
RL == INSTANCE RateLimit WITH
        count          <- allocated,
        window_start   <- window_start,
        clock          <- clock,
        MaxPerWindow   <- Capacity,
        WindowDuration <- WindowDuration,
        MaxClock       <- MaxClock

\* Every construction behavior must map to a RateLimit behavior.
RLRefinement == RL!Spec

\* The configuration checks finite bounds; the proof module establishes the
\* refinement parametrically over the admitted target constant domain.
====
