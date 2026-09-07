---- MODULE RateLimit ----
EXTENDS Naturals

CONSTANTS MaxPerWindow, WindowDuration, MaxClock

\* Admitted constant domain. MaxPerWindow is positive because a fresh-window
\* acquisition sets count to 1. WindowDuration and the finite checking clock
\* bound are natural numbers.
\* Zero duration is a degenerate model case: every TryAcquire resets count to 1,
\* so WindowCountBound holds without throttling. Operational rate limiting
\* requires a positive duration; this model retains the broader constant domain.
ASSUME MaxPerWindowType   == MaxPerWindow \in Nat /\ MaxPerWindow >= 1
ASSUME WindowDurationType == WindowDuration \in Nat
ASSUME MaxClockType       == MaxClock \in Nat

VARIABLES count, window_start, clock

vars == <<count, window_start, clock>>

TypeInvariant ==
    /\ count \in 0..MaxPerWindow
    /\ window_start \in Nat
    /\ clock \in Nat

\* The current window never records more than MaxPerWindow grants.
WindowCountBound ==
    count <= MaxPerWindow

\* The current window anchor is never later than the observed clock.
WindowStartNotFuture ==
    window_start <= clock

Init ==
    /\ count = 0
    /\ window_start = 0
    /\ clock = 0

TryAcquire ==
    IF clock - window_start >= WindowDuration
    THEN /\ window_start' = clock
         /\ count' = 1
         /\ UNCHANGED clock
    ELSE IF count < MaxPerWindow
         THEN /\ count' = count + 1
              /\ UNCHANGED <<window_start, clock>>
         ELSE UNCHANGED vars

Tick ==
    /\ clock < MaxClock
    /\ clock' = clock + 1
    /\ UNCHANGED <<count, window_start>>

Next == TryAcquire \/ Tick

Spec == Init /\ [][Next]_vars

\* RateLimit_Proof proves both semantic state obligations.
====
