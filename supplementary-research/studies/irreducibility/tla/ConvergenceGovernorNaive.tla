---- MODULE ConvergenceGovernorNaive ----
\* Governor WITHOUT gradient phase awareness. A COLD gradient trajectory
\* (never above threshold) causes the governor to declare COOLING. Running
\* this spec with NoCoolingFromCold as an invariant produces the
\* counterexample trace.
\*
\* This module is NOT a decomposition or a mutation of ConvergenceGovernor.
\* It is that machine instrumented with an added observation variable,
\* peak_observed, so that a peak-precondition obligation can be stated over
\* the ungoverned machine: the Update CASE below carries
\* ConvergenceGovernor's five branches and its OTHER unchanged, no mechanism
\* is defused and no guard is removed.  It is the naive-control witness, not
\* the irreducibility witness of any primitive.
\*
\* The checked invariant list does not match ConvergenceGovernor's either.
\* That module's .cfg checks TypeInvariant alone; this one checks
\* NoCoolingFromCold.  The name is ConvergenceGovernorPhaseAware's and the
\* predicate is not: phase-aware states NoCoolingFromCold over
\* gradient_phase, which this machine does not carry, while what is checked
\* here -- state = "COOLING" => peak_observed = TRUE -- is the COOLING limb
\* of phase-aware's ConvergenceRequiresHistory.

EXTENDS Naturals, Sequences

CONSTANTS Threshold, AwakenThreshold, Window, MaxDelta

VARIABLES state, delta_history, peak_observed

vars == <<state, delta_history, peak_observed>>

SumSeq(seq) ==
    LET RECURSIVE Sum(_, _)
        Sum(s, acc) ==
            IF s = <<>> THEN acc
            ELSE Sum(Tail(s), acc + Head(s))
    IN Sum(seq, 0)

Max(a, b) == IF a >= b THEN a ELSE b

Init ==
    /\ state = "ACTIVE"
    /\ delta_history = <<>>
    /\ peak_observed = FALSE

\* Checks ONLY magnitude, not trajectory. No phase awareness, and no
\* peak_observed precondition on COOLING.
Update(delta) ==
    LET new_history ==
            IF Len(delta_history) >= Window
            THEN Append(Tail(delta_history), delta)
            ELSE Append(delta_history, delta)
        avg == SumSeq(new_history) \div Max(Len(new_history), 1)
    IN
    /\ delta_history' = new_history
    /\ peak_observed' = peak_observed \/ (delta >= Threshold)
    /\ state' =
        CASE
            \* The naive transition: enters COOLING on avg < Threshold * 2
            \* alone, without checking whether learning ever started.
            \* A COLD trajectory (all zeros) satisfies this condition immediately.
            state = "ACTIVE" /\ avg < Threshold * 2 -> "COOLING"
          [] state = "COOLING" /\ avg < Threshold -> "CONVERGED"
          [] state = "COOLING" /\ avg >= Threshold * 2 -> "ACTIVE"
          [] state = "CONVERGED" /\ avg > AwakenThreshold -> "AWAKENED"
          [] state = "AWAKENED" /\ avg < Threshold -> "CONVERGED"
          [] OTHER -> state

\* The invariant this machine violates: a governor cannot cool down from a
\* trajectory that was never warm.
NoCoolingFromCold ==
    state = "COOLING" => peak_observed = TRUE

Next == \E d \in 0..MaxDelta : Update(d)

Spec == Init /\ [][Next]_vars

\* TLC finds a violation: a sequence of deltas all below Threshold
\* causes ACTIVE -> COOLING without peak_observed ever becoming TRUE.

====
