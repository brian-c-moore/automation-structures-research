---- MODULE ConvergenceGovernorPhaseAware_NEG_ValidTransitionsProp ----
\* Negative control for ValidTransitionsProp. The marked Update branch permits
\* ACTIVE -> CONVERGED when the post-slide mean exceeds AwakenThreshold, an edge
\* absent from ValidTransitions. With only that property declared, TLC must
\* report it violated. Outside the marked replacement, formulas match the carrier.

EXTENDS Naturals, Sequences

CONSTANTS
    Threshold,
    AwakenThreshold,
    Window,
    MaxDelta

VARIABLES
    state,
    gradient_phase,
    delta_history,
    peak_observed

vars == <<state, gradient_phase, delta_history, peak_observed>>

----

GradientPhases == {"COLD", "WARMING", "ACTIVE_LEARNING", "DECLINING"}
GovernorStates == {"ACTIVE", "COOLING", "CONVERGED", "AWAKENED"}

----

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

ClassifyPhase(delta) ==
    IF ~peak_observed /\ delta < Threshold THEN "COLD"
    ELSE IF ~peak_observed /\ delta >= Threshold THEN "WARMING"
    ELSE IF peak_observed /\ delta >= Threshold THEN "ACTIVE_LEARNING"
    ELSE "DECLINING"

----

TypeInvariant ==
    /\ state \in GovernorStates
    /\ gradient_phase \in GradientPhases
    /\ Len(delta_history) <= Window
    /\ peak_observed \in BOOLEAN

NoCoolingFromCold ==
    state = "COOLING" => gradient_phase /= "COLD"

ConvergedRequiresPeak ==
    state = "CONVERGED" => peak_observed = TRUE

ConvergenceRequiresHistory ==
    state \in {"COOLING", "CONVERGED"} => peak_observed = TRUE

ValidTransitions ==
    /\ state = "ACTIVE" => state' \in {"ACTIVE", "COOLING"}
    /\ state = "COOLING" => state' \in {"COOLING", "CONVERGED", "ACTIVE"}
    /\ state = "CONVERGED" => state' \in {"CONVERGED", "AWAKENED"}
    /\ state = "AWAKENED" => state' \in {"AWAKENED", "CONVERGED"}

ValidTransitionsProp == [][ValidTransitions]_vars

----

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
            state = "ACTIVE" /\ avg < Threshold * 2 /\ new_peak
                -> "COOLING"

          [] state = "ACTIVE" /\ ~new_peak
                -> "ACTIVE"

          [] state = "COOLING" /\ avg < Threshold
                -> "CONVERGED"

          [] state = "COOLING" /\ avg >= Threshold * 2
                -> "ACTIVE"

          [] state = "CONVERGED" /\ avg > AwakenThreshold
                -> "AWAKENED"

          [] state = "AWAKENED" /\ avg < Threshold
                -> "CONVERGED"

\* ---- MUTATION BEGINS -- to the closing marker, this replaces the base text.
            [] state = "ACTIVE" /\ avg > AwakenThreshold
                -> "CONVERGED"

          \* Default: no transition
          [] OTHER -> state
\* ---- MUTATION ENDS.

Next == \E d \in 0..MaxDelta : Update(d)

Spec == Init /\ [][Next]_vars

----

====
