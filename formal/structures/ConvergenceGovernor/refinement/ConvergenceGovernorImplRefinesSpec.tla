---- MODULE ConvergenceGovernorImplRefinesSpec ----
(***************************************************************************)
(* Contract transcription for ConvergenceGovernorPhaseAware. Enum values  *)
(* map to canonical strings; the history Vec maps to a sequence. The avg   *)
(* argument is bound to the post-slide arithmetic mean by the precondition. *)
(***************************************************************************)
\* EXPECT: OK
EXTENDS Naturals, Sequences

CONSTANTS Threshold, AwakenThreshold, Window, MaxDelta
ASSUME ThresholdType == Threshold \in Nat
ASSUME AwakenType == AwakenThreshold \in Nat
ASSUME WindowType == Window \in Nat /\ Window >= 1
ASSUME MaxDeltaType == MaxDelta \in Nat

States == {"ACTIVE", "COOLING", "CONVERGED", "AWAKENED"}
Phases == {"COLD", "WARMING", "ACTIVE_LEARNING", "DECLINING"}
Max(a, b) == IF a >= b THEN a ELSE b
SumSeq(seq) ==
    LET F[i \in 0..Len(seq)] == IF i = 0 THEN 0 ELSE F[i-1] + seq[i]
    IN F[Len(seq)]
Classify(delta, peak) ==
    IF ~peak /\ delta < Threshold THEN "COLD"
    ELSE IF ~peak /\ delta >= Threshold THEN "WARMING"
    ELSE IF peak /\ delta >= Threshold THEN "ACTIVE_LEARNING"
    ELSE "DECLINING"
NewHistory(history, delta) ==
    IF Len(history) >= Window
    THEN Append(Tail(history), delta)
    ELSE Append(history, delta)
NewAverage(history, delta) ==
    SumSeq(NewHistory(history, delta)) \div Max(Len(NewHistory(history, delta)), 1)
NextState(s, avg, new_peak) ==
    CASE s = "ACTIVE" /\ avg < Threshold * 2 /\ new_peak -> "COOLING"
      [] s = "ACTIVE" /\ ~new_peak -> "ACTIVE"
      [] s = "COOLING" /\ avg < Threshold -> "CONVERGED"
      [] s = "COOLING" /\ avg >= Threshold * 2 -> "ACTIVE"
      [] s = "CONVERGED" /\ avg > AwakenThreshold -> "AWAKENED"
      [] s = "AWAKENED" /\ avg < Threshold -> "CONVERGED"
      [] OTHER -> s

VARIABLES threshold, awaken_threshold, window, max_delta,
          state, gradient_phase, delta_history, peak_observed
vars == <<threshold, awaken_threshold, window, max_delta,
          state, gradient_phase, delta_history, peak_observed>>

TypeInvariant ==
    /\ threshold = Threshold
    /\ awaken_threshold = AwakenThreshold
    /\ window = Window
    /\ max_delta = MaxDelta
    /\ state \in States
    /\ gradient_phase \in Phases
    /\ delta_history \in Seq(0..MaxDelta)
    /\ Len(delta_history) <= window
    /\ peak_observed \in BOOLEAN
PeakImplies == state \in {"COOLING", "CONVERGED", "AWAKENED"} => peak_observed
NoCoolingFromCold == state = "COOLING" => gradient_phase /= "COLD"
ConvergenceRequiresHistory ==
    state \in {"COOLING", "CONVERGED"} => peak_observed
ImplInvariant ==
    TypeInvariant /\ PeakImplies /\ NoCoolingFromCold /\ ConvergenceRequiresHistory

Init ==
    /\ threshold = Threshold
    /\ awaken_threshold = AwakenThreshold
    /\ window = Window
    /\ max_delta = MaxDelta
    /\ state = "ACTIVE"
    /\ gradient_phase = "COLD"
    /\ delta_history = <<>>
    /\ peak_observed = FALSE
    /\ ImplInvariant

ImplUpdate(delta) ==
    LET new_history == NewHistory(delta_history, delta)
        avg == NewAverage(delta_history, delta)
        new_phase == Classify(delta, peak_observed)
        new_peak == peak_observed \/ (delta >= threshold)
    IN
    /\ ImplInvariant
    /\ delta \in 0..max_delta
    /\ delta_history' = new_history
    /\ gradient_phase' = new_phase
    /\ peak_observed' = new_peak
    /\ state' = NextState(state, avg, new_peak)
    /\ UNCHANGED <<threshold, awaken_threshold, window, max_delta>>
    /\ ImplInvariant'

ImplRead == UNCHANGED vars
ImplNext == (\E d \in 0..MaxDelta : ImplUpdate(d)) \/ ImplRead
Spec == Init /\ [][ImplNext]_vars

C == INSTANCE ConvergenceGovernorPhaseAware WITH
        Threshold <- Threshold,
        AwakenThreshold <- AwakenThreshold,
        Window <- Window,
        MaxDelta <- MaxDelta,
        state <- state,
        gradient_phase <- gradient_phase,
        delta_history <- delta_history,
        peak_observed <- peak_observed

Refinement == C!Spec
====
