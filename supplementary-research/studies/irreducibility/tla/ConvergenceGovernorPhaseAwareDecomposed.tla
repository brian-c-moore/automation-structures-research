--------------- MODULE ConvergenceGovernorPhaseAwareDecomposed ---------------
(* Splits ConvergenceGovernorPhaseAware's Update: EvaluateUpdate computes its
   LET (history, phase, peak, CASE target) and holds it; CommitUpdate applies
   its writes. With two updaters a stale commit steps the state graph illegally,
   violating ValidTransitionsProp. Adds `pc` and `held`; config is the
   carrier's. *)
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
    peak_observed,
    pc,
    held

vars == <<state, gradient_phase, delta_history, peak_observed, pc, held>>

Procs == {"u1", "u2"}

GradientPhases == {"COLD", "WARMING", "ACTIVE_LEARNING", "DECLINING"}
GovernorStates == {"ACTIVE", "COOLING", "CONVERGED", "AWAKENED"}

Max(a, b) == IF a >= b THEN a ELSE b

SumSeq(seq) ==
    LET F[i \in 0..Len(seq)] ==
            IF i = 0 THEN 0
            ELSE F[i-1] + seq[i]
    IN  F[Len(seq)]

AvgDelta ==
    IF Len(delta_history) = 0 THEN 0
    ELSE SumSeq(delta_history) \div Len(delta_history)

ClassifyPhase(delta) ==
    IF ~peak_observed /\ delta < Threshold THEN "COLD"
    ELSE IF ~peak_observed /\ delta >= Threshold THEN "WARMING"
    ELSE IF peak_observed /\ delta >= Threshold THEN "ACTIVE_LEARNING"
    ELSE "DECLINING"

TypeInvariant ==
    /\ state \in GovernorStates
    /\ gradient_phase \in GradientPhases
    /\ Len(delta_history) <= Window
    /\ peak_observed \in BOOLEAN

NoCoolingFromCold ==
    state = "COOLING" => gradient_phase /= "COLD"

NoSkipping ==
    state = "CONVERGED" => peak_observed = TRUE

ConvergenceRequiresHistory ==
    state \in {"COOLING", "CONVERGED"} => peak_observed = TRUE

ValidTransitions ==
    /\ state = "ACTIVE" => state' \in {"ACTIVE", "COOLING"}
    /\ state = "COOLING" => state' \in {"COOLING", "CONVERGED", "ACTIVE"}
    /\ state = "CONVERGED" => state' \in {"CONVERGED", "AWAKENED"}
    /\ state = "AWAKENED" => state' \in {"AWAKENED", "CONVERGED"}

ValidTransitionsProp == [][ValidTransitions]_vars

Init ==
    /\ state = "ACTIVE"
    /\ gradient_phase = "COLD"
    /\ delta_history = <<>>
    /\ peak_observed = FALSE
    /\ pc = [p \in Procs |-> "idle"]
    /\ held = [p \in Procs |-> [history |-> <<>>, phase |-> "COLD",
                                peak |-> FALSE, target |-> "ACTIVE"]]

(* Step 1: canonical Update's LET -- the record it would write, computed
   from the current state and held; no mutation *)
EvaluateUpdate(p, delta) ==
    /\ pc[p] = "idle"
    /\ LET new_history ==
               IF Len(delta_history) >= Window
               THEN Append(Tail(delta_history), delta)
               ELSE Append(delta_history, delta)
           avg == SumSeq(new_history) \div Max(Len(new_history), 1)
           new_phase == ClassifyPhase(delta)
           new_peak == peak_observed \/ (delta >= Threshold)
           target ==
               CASE state = "ACTIVE" /\ avg < Threshold * 2 /\ new_peak
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
                 [] OTHER -> state
       IN held' = [held EXCEPT ![p] = [history |-> new_history, phase |-> new_phase,
                                       peak |-> new_peak, target |-> target]]
    /\ pc' = [pc EXCEPT ![p] = "evaluated"]
    /\ UNCHANGED <<state, gradient_phase, delta_history, peak_observed>>

(* Step 2: canonical Update's four writes, from the held record *)
CommitUpdate(p) ==
    /\ pc[p] = "evaluated"
    /\ delta_history' = held[p].history
    /\ gradient_phase' = held[p].phase
    /\ peak_observed' = held[p].peak
    /\ state' = held[p].target
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED held

Next ==
    \/ \E p \in Procs, d \in 0..MaxDelta : EvaluateUpdate(p, d)
    \/ \E p \in Procs : CommitUpdate(p)

Spec == Init /\ [][Next]_vars
=============================================================================
