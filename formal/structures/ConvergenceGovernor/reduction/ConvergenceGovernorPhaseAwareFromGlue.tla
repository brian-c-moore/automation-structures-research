---- MODULE ConvergenceGovernorPhaseAwareFromGlue ----
\* State-variable relabeling of ConvergenceGovernorPhaseAware. The construction
\* retains governor state, phase, history, and the peak latch directly; it does
\* not retain state from another primitive.
\*
\* NoCoolingFromCold, ConvergedRequiresPeak, ConvergenceRequiresHistory, and
\* ValidTransitionsProp are stated over those variables. The refinement proves
\* equivalence under relabeling; it does not show that another component
\* supplies the governor obligations. TypeInvariant owns the window bound.

EXTENDS Naturals, Sequences

CONSTANTS Threshold, AwakenThreshold, Window, MaxDelta

GradientPhases == {"COLD", "WARMING", "ACTIVE_LEARNING", "DECLINING"}
GovernorStates == {"ACTIVE", "COOLING", "CONVERGED", "AWAKENED"}

\* Relabeled carrier state.
VARIABLES g_state,
          g_phase,
          g_history,   \* bounded sliding window with oldest-entry removal
          g_peak       \* threshold-history latch

vars == <<g_state, g_phase, g_history, g_peak>>

Max(a, b) == IF a >= b THEN a ELSE b

SumSeq(seq) ==
    LET F[i \in 0..Len(seq)] ==
            IF i = 0 THEN 0
            ELSE F[i-1] + seq[i]
    IN  F[Len(seq)]

\* Arithmetic mean of the retained window.
AvgDelta ==
    IF Len(g_history) = 0 THEN 0
    ELSE SumSeq(g_history) \div Len(g_history)

TypeInvariant ==
    /\ g_state \in GovernorStates
    /\ g_phase \in GradientPhases
    /\ Len(g_history) <= Window
    /\ g_peak \in BOOLEAN

\* Carrier obligations restated over the relabeled state.
MappedNoCoolingFromCold ==
    g_state = "COOLING" => g_phase /= "COLD"

MappedConvergedRequiresPeak ==
    g_state = "CONVERGED" => g_peak = TRUE

MappedConvergenceRequiresHistory ==
    g_state \in {"COOLING", "CONVERGED"} => g_peak = TRUE

ClassifyPhase(delta) ==
    IF ~g_peak /\ delta < Threshold THEN "COLD"
    ELSE IF ~g_peak /\ delta >= Threshold THEN "WARMING"
    ELSE IF g_peak /\ delta >= Threshold THEN "ACTIVE_LEARNING"
    ELSE "DECLINING"

Init ==
    /\ g_state   = "ACTIVE"
    /\ g_phase   = "COLD"
    /\ g_history = <<>>
    /\ g_peak    = FALSE

\* The target's own action, carried verbatim over the glue.
Update(delta) ==
    LET new_history ==
            IF Len(g_history) >= Window
            THEN Append(Tail(g_history), delta)
            ELSE Append(g_history, delta)
        avg == SumSeq(new_history) \div Max(Len(new_history), 1)
        new_phase == ClassifyPhase(delta)
        new_peak == g_peak \/ (delta >= Threshold)
    IN
    /\ g_history' = new_history
    /\ g_phase'   = new_phase
    /\ g_peak'    = new_peak
    /\ g_state' =
        CASE
            g_state = "ACTIVE" /\ avg < Threshold * 2 /\ new_peak
                -> "COOLING"
          [] g_state = "ACTIVE" /\ ~new_peak
                -> "ACTIVE"
          [] g_state = "COOLING" /\ avg < Threshold
                -> "CONVERGED"
          [] g_state = "COOLING" /\ avg >= Threshold * 2
                -> "ACTIVE"
          [] g_state = "CONVERGED" /\ avg > AwakenThreshold
                -> "AWAKENED"
          [] g_state = "AWAKENED" /\ avg < Threshold
                -> "CONVERGED"
          [] OTHER -> g_state

Next == \E d \in 0..MaxDelta : Update(d)

Spec == Init /\ [][Next]_vars

\* --- Refinement mapping to ConvergenceGovernorPhaseAware ------------------
CG == INSTANCE ConvergenceGovernorPhaseAware WITH
        state           <- g_state,
        gradient_phase  <- g_phase,
        delta_history   <- g_history,
        peak_observed   <- g_peak,
        Threshold       <- Threshold,
        AwakenThreshold <- AwakenThreshold,
        Window          <- Window,
        MaxDelta        <- MaxDelta

ConvergenceGovernorRefinement == CG!Spec
====
