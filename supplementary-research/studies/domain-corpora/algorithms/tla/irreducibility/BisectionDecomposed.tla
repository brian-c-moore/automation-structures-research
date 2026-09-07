---- MODULE BisectionDecomposed ----
(*
  Bisection separated into TraversalEngine-over-binary-probe-tree plus
  per-probe ActuationPass.

  The primitive Bisection atomically evaluates P(mid) and narrows [lo,hi] in
  one step, so the halving invariant (lo<=Threshold<=hi) is maintained at
  every observable state.

  In the decomposed model, TraversalEngine visits probe points in the binary
  probe tree independently of the current interval.  It records in a shared
  slot (probe_point, probe_dir) the probe it is visiting.  The ActuationPass
  then performs the interval update using that slot.  Because TraversalEngine
  is an autonomous engine that walks its own tree, it may visit probe points
  that are NOT the midpoint of the current [lo,hi] interval — the engine has
  no notion of the ordered domain; it only walks the tree.

  This separates the "which point to probe" decision (TraversalEngine) from
  the "evaluate P and update bounds" action (ActuationPass), losing the
  ordered-domain constraint that binds mid = (lo+hi)/2.

  The TraversalEngine visits all nodes in the probe tree {0..DomainSize-1}.
  For each node v it can record:
    - probe_dir = "left"  (meaning P(v) = FALSE → update hi = v)
    - probe_dir = "right" (meaning P(v) = TRUE  → update lo = v+1)

  But since TraversalEngine is not aware of Threshold, it can record either
  direction for any probe point.  ActuationPass blindly applies whichever is
  in the slot.  If TraversalEngine records probe_dir="left" for a probe point
  v < Threshold, the ActuationPass sets hi=v < Threshold, and Halving is
  violated.

  Expected VIOLATION of: Halving

  ---------------------------------------------------------------------------
  What this instrument pairs with, and a naming divergence to read before
  citing it.

  The positive half of this qualification pair is the CANONICAL Bisection
  entry, resolved through the verification runner's TLA module search path.

  `Halving` BELOW IS NOT CANONICAL'S `Halving`.  What this module defines and
  breaks under that name --
        lo <= Threshold /\ Threshold <= hi
  -- is the threshold-straddle property, which canonical states, checks and
  PROVES under the name `MonotonicityPreservation`.  Canonical's `Halving` is a
  different property: the per-probe contraction action property
  [][ContractionStep]_vars, whose own decomposition is the separate instrument
  supplementary-research/studies/irreducibility/tla/BisectionDecomposed.tla,
  which splits counting from narrowing.  The two decompositions test DIFFERENT atomicity
  claims and neither subsumes the other:
    - this one: choosing the probe point and applying the update must be one
      step, or the interval can stop straddling the threshold;
    - canonical's: counting a probe and narrowing the interval must be one
      step, or the contraction rate is violated.
  The name below is the one this module's recorded verdict was produced
  under, and it is kept for that reason.
  ---------------------------------------------------------------------------
*)
EXTENDS Naturals

CONSTANTS
    DomainSize,   \* size of the domain
    Threshold,    \* the threshold (in 1..DomainSize-1)
    MaxProbes     \* bound on probe count (part of spec)

VARIABLES
    lo,          \* lower bound of candidate interval
    hi,          \* upper bound of candidate interval
    probe_point, \* the probe node currently staged by TraversalEngine (0 = none)
    probe_dir,   \* "left" | "right" | "none" — direction staged by engine
    probes_done  \* count of actuations completed

vars == <<lo, hi, probe_point, probe_dir, probes_done>>

\* ---- Invariant under test -------------------------------------------------

\* The interval must always contain the threshold.
\* In the atomic primitive this is maintained after every step.
\* Under decomposition, ActuationPass can apply a direction that is
\* inconsistent with the actual threshold, breaking this invariant.
Halving ==
    /\ lo <= Threshold
    /\ Threshold <= hi

\* ---- Init -----------------------------------------------------------------

Init ==
    /\ lo = 0
    /\ hi = DomainSize
    /\ probe_point = 0
    /\ probe_dir = "none"
    /\ probes_done = 0

\* ---- TraversalEngine: stage a probe point ---------------------------------
\* The engine visits any point in 0..DomainSize-1 and records any direction.
\* It does NOT check whether the point is the actual midpoint of [lo,hi].
\* It does NOT consult Threshold.

StageProbe(v, d) ==
    /\ probe_dir = "none"          \* slot is free
    /\ probes_done < MaxProbes
    /\ v \in 0..DomainSize-1
    /\ d \in {"left", "right"}
    /\ probe_point' = v
    /\ probe_dir' = d
    /\ UNCHANGED <<lo, hi, probes_done>>

\* ---- ActuationPass: apply the staged probe --------------------------------
\* Blindly applies the direction recorded by StageProbe.

ActuateProbe ==
    /\ probe_dir /= "none"
    /\ hi - lo >= 2
    /\ \/ (probe_dir = "left"  /\ hi' = probe_point /\ lo' = lo)
       \/ (probe_dir = "right" /\ lo' = probe_point + 1 /\ hi' = hi)
    /\ probe_dir' = "none"
    /\ probe_point' = 0
    /\ probes_done' = probes_done + 1

Converged ==
    /\ hi - lo < 2
    /\ UNCHANGED vars

Next ==
    \/ \E v \in 0..DomainSize-1, d \in {"left", "right"} : StageProbe(v, d)
    \/ ActuateProbe
    \/ Converged

Spec == Init /\ [][Next]_vars
=============================================================================
