---- MODULE ConvergenceGovernorPhaseAware ----
EXTENDS Naturals, Sequences

CONSTANTS
    Threshold,          \* Threshold used by phase classification and state transitions
    AwakenThreshold,    \* Post-convergence reactivation threshold
    Window,             \* Maximum sliding-window length
    MaxDelta            \* Upper bound on an input delta

VARIABLES
    state,              \* Governor state: ACTIVE, COOLING, CONVERGED, AWAKENED
    gradient_phase,     \* Qualitative gradient trajectory: COLD, WARMING, ACTIVE_LEARNING, DECLINING
    delta_history,      \* Recent gradient magnitudes
    peak_observed       \* Whether an observed delta has met or exceeded Threshold

vars == <<state, gradient_phase, delta_history, peak_observed>>

----

\* The phase combines the pre-step peak latch with the current delta. COLD and
\* DECLINING distinguish a sub-threshold delta before and after the latch is
\* set. These labels do not assert monotonicity of the delta sequence.

GradientPhases == {"COLD", "WARMING", "ACTIVE_LEARNING", "DECLINING"}
GovernorStates == {"ACTIVE", "COOLING", "CONVERGED", "AWAKENED"}

----

\* === Helper ===

Max(a, b) == IF a >= b THEN a ELSE b

SumSeq(seq) ==
    LET F[i \in 0..Len(seq)] ==
            IF i = 0 THEN 0
            ELSE F[i-1] + seq[i]
    IN  F[Len(seq)]

AvgDelta ==
    IF Len(delta_history) = 0 THEN 0
    ELSE SumSeq(delta_history) \div Len(delta_history)

----

\* === Phase Classification ===
\* Classify the current delta relative to Threshold and the pre-step latch.

ClassifyPhase(delta) ==
    \* COLD: no earlier or current delta has reached Threshold.
    IF ~peak_observed /\ delta < Threshold THEN "COLD"
    \* WARMING: the current delta is the first to reach Threshold.
    ELSE IF ~peak_observed /\ delta >= Threshold THEN "WARMING"
    \* ACTIVE_LEARNING: the latch is already set and the current delta is high.
    ELSE IF peak_observed /\ delta >= Threshold THEN "ACTIVE_LEARNING"
    \* DECLINING: the latch is set and the current delta is sub-threshold.
    ELSE "DECLINING"

----

\* === Safety Invariants ===

TypeInvariant ==
    /\ state \in GovernorStates
    /\ gradient_phase \in GradientPhases
    /\ Len(delta_history) <= Window
    /\ peak_observed \in BOOLEAN

\* A COOLING state cannot carry the pre-threshold COLD phase.
NoCoolingFromCold ==
    state = "COOLING" => gradient_phase /= "COLD"

\* Derived CONVERGED-only view of ConvergenceRequiresHistory. It remains a
\* named semantic corollary for readers and executable correspondence, but is
\* not an independent checked invariant or control seam.
ConvergedRequiresPeak ==
    state = "CONVERGED" => peak_observed = TRUE

\* COOLING and CONVERGED both require a prior or current threshold event.
ConvergenceRequiresHistory ==
    state \in {"COOLING", "CONVERGED"} => peak_observed = TRUE

ConvergedRequiresPeakDerived ==
    ConvergenceRequiresHistory => ConvergedRequiresPeak

\* The allowed state-transition graph: a two-state (action) constraint -- the
\* governor only ever steps along it -- so it is checked by TLC as the PROPERTY
\* ValidTransitionsProp and proved in the _Proof module.
ValidTransitions ==
    /\ state = "ACTIVE" => state' \in {"ACTIVE", "COOLING"}
    /\ state = "COOLING" => state' \in {"COOLING", "CONVERGED", "ACTIVE"}
    /\ state = "CONVERGED" => state' \in {"CONVERGED", "AWAKENED"}
    /\ state = "AWAKENED" => state' \in {"AWAKENED", "CONVERGED"}

ValidTransitionsProp == [][ValidTransitions]_vars

----

\* === Operations ===

Init ==
    /\ state = "ACTIVE"
    /\ gradient_phase = "COLD"
    /\ delta_history = <<>>
    /\ peak_observed = FALSE

Update(delta) ==
    LET new_history ==
            IF Len(delta_history) >= Window
            THEN Append(Tail(delta_history), delta)
            ELSE Append(delta_history, delta)
        avg == SumSeq(new_history) \div Max(Len(new_history), 1)
        new_phase == ClassifyPhase(delta)
        new_peak == peak_observed \/ (delta >= Threshold)
    IN
    /\ delta_history' = new_history
    /\ gradient_phase' = new_phase
    /\ peak_observed' = new_peak
    /\ state' =
        CASE
            \* ACTIVE -> COOLING when the post-slide mean is below twice the
            \* threshold and the post-step peak latch is set.
            state = "ACTIVE" /\ avg < Threshold * 2 /\ new_peak
                -> "COOLING"

            \* ACTIVE stays ACTIVE while the post-step peak latch is unset.
          [] state = "ACTIVE" /\ ~new_peak
                -> "ACTIVE"

            \* COOLING -> CONVERGED when the post-slide mean is sub-threshold.
          [] state = "COOLING" /\ avg < Threshold
                -> "CONVERGED"

            \* COOLING -> ACTIVE when the post-slide mean reaches twice Threshold.
          [] state = "COOLING" /\ avg >= Threshold * 2
                -> "ACTIVE"

            \* CONVERGED -> AWAKENED above the reactivation threshold.
          [] state = "CONVERGED" /\ avg > AwakenThreshold
                -> "AWAKENED"

            \* AWAKENED -> CONVERGED when the mean becomes sub-threshold.
          [] state = "AWAKENED" /\ avg < Threshold
                -> "CONVERGED"

            \* Default: no transition
          [] OTHER -> state

Next == \E d \in 0..MaxDelta : Update(d)

Spec == Init /\ [][Next]_vars

----

\* === Theorems ===

\* The two independent invariants exclude a COLD phase in COOLING and require
\* the peak latch in COOLING or CONVERGED. ConvergedRequiresPeak is the named
\* CONVERGED-only corollary of ConvergenceRequiresHistory.
\* Spec => [](NoCoolingFromCold /\ ConvergenceRequiresHistory /\ ConvergedRequiresPeak):
\* proved as SafetyOriginal in ConvergenceGovernorPhaseAware_Proof.tla
\* (verbatim restatement).

\* The governor only ever steps along the allowed transition graph (an action
\* property; checked by TLC as PROPERTY ValidTransitionsProp).
\* Spec => ValidTransitionsProp: proved as ValidTransitionsSafety in
\* ConvergenceGovernorPhaseAware_Proof.tla.

====
