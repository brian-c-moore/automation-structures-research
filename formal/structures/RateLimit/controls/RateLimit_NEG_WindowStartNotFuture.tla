---- MODULE RateLimit_NEG_WindowStartNotFuture ----
\* Negative control for WindowStartNotFuture. A rollover anchors the new
\* window at clock + 1 while leaving clock unchanged.

EXTENDS Naturals

CONSTANTS MaxPerWindow, WindowDuration, MaxClock

ASSUME MaxPerWindowType   == MaxPerWindow \in Nat /\ MaxPerWindow >= 1
ASSUME WindowDurationType == WindowDuration \in Nat
ASSUME MaxClockType       == MaxClock \in Nat

VARIABLES count, window_start, clock

vars == <<count, window_start, clock>>

TypeInvariant ==
    /\ count \in 0..MaxPerWindow
    /\ window_start \in Nat
    /\ clock \in Nat

WindowCountBound ==
    count <= MaxPerWindow

WindowStartNotFuture ==
    window_start <= clock

Init ==
    /\ count = 0
    /\ window_start = 0
    /\ clock = 0

TryAcquire ==
    IF clock - window_start >= WindowDuration
\* ---- MUTATION BEGINS -- to the closing marker, this replaces the base text.
    THEN /\ window_start' = clock + 1
         /\ count' = 1
\* ---- MUTATION ENDS.
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

====
