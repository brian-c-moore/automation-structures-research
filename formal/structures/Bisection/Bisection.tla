---- MODULE Bisection ----
(*
  Bisection<D,P>
  Models ordered domain D = 0..DomainSize-1, monotonic predicate P over D.
  P(x) is TRUE for x < Threshold and FALSE for x >= Threshold.
  (Threshold is an opaque CONSTANT in 1..DomainSize-1.)
  The primitive maintains a candidate interval [lo, hi] and halves it per probe.

  Properties:
    Halving (PROPERTY)     — per-probe contraction: every probe at least halves
                             the interval, probes_taken' > probes_taken =>
                             hi' - lo' <= (hi - lo) \div 2.
    MonotonicityPreservation (INVARIANT) — [lo, hi] always straddles the
                             threshold: lo <= Threshold /\ Threshold <= hi.
    ProbeBound (INVARIANT)   — probes_taken <= MaxProbes; the safety bound.
    EventualConvergence (PROPERTY) — under WF fairness the interval eventually
                             narrows to a point, <>(hi - lo < 2).
*)
EXTENDS Naturals

CONSTANTS
    DomainSize,    \* size of the ordered domain
    Threshold,     \* the target boundary for P
    MaxProbes      \* the probe budget

\* Powers of two, as a function, so the probe budget the domain requires can be
\* stated below without a logarithm.
Pow2[k \in Nat] == IF k = 0 THEN 1 ELSE 2 * Pow2[k - 1]

\* The constant valuations this specification describes. They are stated here
\* rather than only in the proof, because an assumption carried by a proof
\* alone bounds what is proved while leaving the module itself satisfiable at
\* constants that falsify its own invariants. DomainFitsProbes is the one
\* ProbeBound rests on: bisection is logarithmic, so a probe budget smaller
\* than the number of halvings the domain takes admits a run in which
\* probes_taken passes MaxProbes.
ASSUME DomainSizeType   == DomainSize \in Nat /\ DomainSize >= 2
ASSUME MaxProbesType    == MaxProbes \in Nat
ASSUME ThresholdType    == Threshold \in 1..(DomainSize - 1)
ASSUME DomainFitsProbes == DomainSize <= Pow2[MaxProbes]

VARIABLES
    lo,           \* lower bound of candidate interval (inclusive)
    hi,           \* upper bound of candidate interval (inclusive)
    probes_taken  \* number of probes completed so far

vars == <<lo, hi, probes_taken>>

\* ---- Type invariant -------------------------------------------------------

TypeInvariant ==
    /\ lo \in 0..DomainSize
    /\ hi \in 0..DomainSize
    /\ probes_taken \in Nat

\* ---- Safety invariants ----------------------------------------------------

\* Per-probe contraction is a two-state property: every probe at least halves
\* the interval width.
ContractionStep ==
    probes_taken' > probes_taken => hi' - lo' <= (hi - lo) \div 2

Halving ==
    [][ContractionStep]_vars

\* The threshold is always within [lo, hi].
MonotonicityPreservation ==
    /\ lo <= Threshold
    /\ Threshold <= hi

\* Number of probes taken never passes the budget. It is DomainFitsProbes that
\* makes this a claim about every valuation admitted by the module assumptions,
\* rather than only the finite configuration used by TLC.
ProbeBound ==
    probes_taken <= MaxProbes

\* ---- Init -----------------------------------------------------------------
\* Allow any valid initial interval to make TLC explore all reachable
\* bisection states (not just the single start-of-search state).
\* Constraint: lo <= Threshold <= hi (MonotonicityPreservation from the start),
\* and probes_taken reflects a plausible probe count so far.

Init ==
    /\ lo \in 0..Threshold
    /\ hi \in Threshold..DomainSize
    /\ probes_taken = 0

\* ---- Actions --------------------------------------------------------------

\* Mid-point of [lo, hi].
Mid == (lo + hi) \div 2

\* Probe the midpoint and narrow the interval.  Two cases based on P(Mid):
\*   P(Mid) = FALSE iff Mid >= Threshold → threshold is in [lo, Mid]  → hi' = Mid
\*   P(Mid) = TRUE  iff Mid < Threshold  → threshold is in [Mid+1, hi] → lo' = Mid+1
\* Guard: hi - lo >= 2 ensures there is still a non-trivial interval to narrow.

ProbeLeft ==
    \* P(Mid) = FALSE: threshold is in [lo, Mid]
    /\ hi - lo >= 2
    /\ Mid >= Threshold
    /\ hi' = Mid
    /\ lo' = lo
    /\ probes_taken' = probes_taken + 1

ProbeRight ==
    \* P(Mid) = TRUE: threshold is in [Mid+1, hi]
    /\ hi - lo >= 2
    /\ Mid < Threshold
    /\ lo' = Mid + 1
    /\ hi' = hi
    /\ probes_taken' = probes_taken + 1

\* Terminal state: interval has been narrowed to a point; stutter.
Converged ==
    /\ hi - lo < 2
    /\ UNCHANGED vars

Next ==
    \/ ProbeLeft
    \/ ProbeRight
    \/ Converged

\* Fairness: weak fairness on the probe actions so the bisection makes progress.
Spec == Init /\ [][Next]_vars /\ WF_vars(ProbeLeft \/ ProbeRight)

\* Eventual convergence: under fairness the interval is eventually narrowed to a
\* point (hi - lo < 2). The liveness companion to the ProbeBound invariant.
EventualConvergence ==
    <>(hi - lo < 2)

\* Bisection_Proof proves the public safety, contraction, and convergence
\* properties. EventualConvergence uses downward induction on the remaining
\* probe budget under the weak-fairness premise in Spec.
====
