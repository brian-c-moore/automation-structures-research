------------------------ MODULE BisectionDecomposed -------------------------
(* Decomposition of Bisection.

   Canonical Bisection narrows the interval AND counts the probe in one ATOMIC
   step (ProbeLeft / ProbeRight), so the per-probe contraction holds:
       probes_taken' > probes_taken => hi' - lo' <= (hi - lo) \div 2.

   This decomposition splits that atomic step into two separable steps:
     CountProbe    -- increment probes_taken (a probe is "taken")
     NarrowInterval -- then narrow the interval to the midpoint.
   Between them the probe has been COUNTED but the interval has NOT yet
   contracted (lo, hi unchanged), so the CountProbe step exhibits
   probes_taken' > probes_taken with hi' - lo' = hi - lo > (hi - lo) \div 2:
   the per-probe contraction is violated.  This is the TOCTOU window the
   primitive's atomicity closes; TLC finds the counterexample.                *)
EXTENDS Naturals

CONSTANTS DomainSize, Threshold

VARIABLES lo, hi, probes_taken, pc

vars == <<lo, hi, probes_taken, pc>>

\* Mid-point of [lo, hi] (the canonical midpoint).
Mid == (lo + hi) \div 2

Init ==
    /\ lo \in 0..Threshold
    /\ hi \in Threshold..DomainSize
    /\ probes_taken = 0
    /\ pc = "idle"

\* Step 1: COUNT the probe without narrowing the interval.  The canonical
\* ProbeLeft/ProbeRight does the count and the narrowing together.
CountProbe ==
    /\ pc = "idle"
    /\ hi - lo >= 2
    /\ probes_taken' = probes_taken + 1
    /\ pc' = "narrowing"
    /\ UNCHANGED <<lo, hi>>

\* Step 2: NARROW the interval (the midpoint is unchanged since CountProbe left
\* lo, hi alone), using the canonical direction rule on P(Mid) = (Mid >= Threshold).
NarrowInterval ==
    /\ pc = "narrowing"
    /\ hi' = (IF Mid >= Threshold THEN Mid ELSE hi)
    /\ lo' = (IF Mid >= Threshold THEN lo ELSE Mid + 1)
    /\ pc' = "idle"
    /\ UNCHANGED probes_taken

\* Terminal state: interval narrowed to a point; stutter.
Converged ==
    /\ pc = "idle"
    /\ hi - lo < 2
    /\ UNCHANGED vars

Next ==
    \/ CountProbe
    \/ NarrowInterval
    \/ Converged

Spec == Init /\ [][Next]_vars

\* The per-probe contraction.  TLC finds it violated by the CountProbe step.
ContractionStep ==
    probes_taken' > probes_taken => hi' - lo' <= (hi - lo) \div 2

Halving ==
    [][ContractionStep]_vars
=============================================================================
