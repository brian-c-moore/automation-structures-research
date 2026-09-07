---- MODULE Bisection_NEG_ProbeBound ----
\* Negative control for ProbeBound. Mid removes only one point per left probe,
\* so a permitted search can exceed MaxProbes.

EXTENDS Naturals

CONSTANTS
    DomainSize,
    Threshold,
    MaxProbes

Pow2[k \in Nat] == IF k = 0 THEN 1 ELSE 2 * Pow2[k - 1]

ASSUME DomainSizeType   == DomainSize \in Nat /\ DomainSize >= 2
ASSUME MaxProbesType    == MaxProbes \in Nat
ASSUME ThresholdType    == Threshold \in 1..(DomainSize - 1)
ASSUME DomainFitsProbes == DomainSize <= Pow2[MaxProbes]

VARIABLES
    lo,
    hi,
    probes_taken

vars == <<lo, hi, probes_taken>>

TypeInvariant ==
    /\ lo \in 0..DomainSize
    /\ hi \in 0..DomainSize
    /\ probes_taken \in Nat

ContractionStep ==
    probes_taken' > probes_taken => hi' - lo' <= (hi - lo) \div 2

Halving ==
    [][ContractionStep]_vars

MonotonicityPreservation ==
    /\ lo <= Threshold
    /\ Threshold <= hi

ProbeBound ==
    probes_taken <= MaxProbes

Init ==
    /\ lo \in 0..Threshold
    /\ hi \in Threshold..DomainSize
    /\ probes_taken = 0

\* ---- MUTATION BEGINS -- to the closing marker, this replaces the base text.
Mid == hi - 1
\* ---- MUTATION ENDS.

ProbeLeft ==
    /\ hi - lo >= 2
    /\ Mid >= Threshold
    /\ hi' = Mid
    /\ lo' = lo
    /\ probes_taken' = probes_taken + 1

ProbeRight ==
    /\ hi - lo >= 2
    /\ Mid < Threshold
    /\ lo' = Mid + 1
    /\ hi' = hi
    /\ probes_taken' = probes_taken + 1

Converged ==
    /\ hi - lo < 2
    /\ UNCHANGED vars

Next ==
    \/ ProbeLeft
    \/ ProbeRight
    \/ Converged

Spec == Init /\ [][Next]_vars /\ WF_vars(ProbeLeft \/ ProbeRight)

EventualConvergence ==
    <>(hi - lo < 2)

====
