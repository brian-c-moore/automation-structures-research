---- MODULE RateLimitImplRefinesSpec_NEG ----
(***************************************************************************)
(* Isolated frame fault: Tick also moves window_start to the new clock.     *)
(* Typing and both public bounds remain checked; the canonical Tick frame   *)
(* is the failing refinement seam.                                          *)
(***************************************************************************)
\* EXPECT: VIOLATION
EXTENDS RateLimitImplRefinesSpec

AdjacentInvariant == ImplInvariant
FaultTick ==
    /\ AdjacentInvariant
    /\ clock < max_clock
    /\ clock' = clock + 1
    /\ window_start' = clock + 1
    /\ UNCHANGED <<max_per_window, window_duration, max_clock, count>>
    /\ AdjacentInvariant'

FaultNext == ImplTryAcquire \/ FaultTick \/ ImplRead
FaultRefinement == R!Spec
====
