---- MODULE RateLimitImplRefinesSpec ----
(***************************************************************************)
(* Contract transcription for the Verus RateLimit carrier.                *)
(* max_per_window, window_duration, and max_clock are immutable fields and *)
(* map to the canonical constants. The remaining three u64 fields map      *)
(* identically to natural-number state. Rejected try_acquire calls and      *)
(* read-only observations stutter.                                         *)
(***************************************************************************)
\* EXPECT: OK
EXTENDS Naturals

CONSTANTS MaxPerWindow, WindowDuration, MaxClock
ASSUME MaxPerWindowType == MaxPerWindow \in Nat /\ MaxPerWindow >= 1
ASSUME WindowDurationType == WindowDuration \in Nat
ASSUME MaxClockType == MaxClock \in Nat

VARIABLES max_per_window, window_duration, max_clock,
          count, window_start, clock
vars == <<max_per_window, window_duration, max_clock,
          count, window_start, clock>>

TypeInvariant ==
    /\ max_per_window = MaxPerWindow
    /\ window_duration = WindowDuration
    /\ max_clock = MaxClock
    /\ count \in 0..max_per_window
    /\ window_start \in Nat
    /\ clock \in Nat
WindowCountBound == count <= max_per_window
WindowStartNotFuture == window_start <= clock
ImplInvariant == TypeInvariant /\ WindowCountBound /\ WindowStartNotFuture

Init ==
    /\ max_per_window = MaxPerWindow
    /\ window_duration = WindowDuration
    /\ max_clock = MaxClock
    /\ count = 0
    /\ window_start = 0
    /\ clock = 0
    /\ ImplInvariant

ImplTryAcquire ==
    /\ ImplInvariant
    /\ IF clock - window_start >= window_duration
       THEN /\ window_start' = clock
            /\ count' = 1
            /\ UNCHANGED clock
       ELSE IF count < max_per_window
            THEN /\ count' = count + 1
                 /\ UNCHANGED <<window_start, clock>>
            ELSE UNCHANGED <<count, window_start, clock>>
    /\ UNCHANGED <<max_per_window, window_duration, max_clock>>
    /\ ImplInvariant'

ImplTick ==
    /\ ImplInvariant
    /\ clock < max_clock
    /\ clock' = clock + 1
    /\ UNCHANGED <<max_per_window, window_duration, max_clock,
                    count, window_start>>
    /\ ImplInvariant'

ImplRead == UNCHANGED vars
ImplNext == ImplTryAcquire \/ ImplTick \/ ImplRead
Spec == Init /\ [][ImplNext]_vars

R == INSTANCE RateLimit WITH
        MaxPerWindow <- MaxPerWindow,
        WindowDuration <- WindowDuration,
        MaxClock <- MaxClock,
        count <- count,
        window_start <- window_start,
        clock <- clock

Refinement == R!Spec
====
