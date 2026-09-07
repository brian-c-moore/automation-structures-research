---- MODULE ConvergenceGovernorPhaseAware_Proof ----
(***************************************************************************
  TLAPS proof of safety for the phase-aware convergence governor.

  Proves, for ConvergenceGovernorPhaseAware, the independent invariants:

      Spec => [](NoCoolingFromCold /\ ConvergenceRequiresHistory)

  as SafetyOriginal, and each conjunct separately; the remaining checked
  invariant, TypeInvariant, as TypeSafety; and the checked action property
  ValidTransitionsProp as ValidTransitionsSafety. ConvergedRequiresPeakSafety
  is retained only as an explicit corollary of ConvergenceRequiresHistory.

  Inductive strengthening: ConvergenceRequiresHistory (state in COOLING/
  CONVERGED => peak) is too weak alone; it does not constrain "AWAKENED",
  which AWAKENED <-> CONVERGED transitions need. The natural strengthening
  that strengthens ConvergenceRequiresHistory across AWAKENED is

      WarmStateRequiresPeak ==
         state \in {"COOLING", "CONVERGED", "AWAKENED"} => peak_observed = TRUE

  which is inductive once combined with TypeInvariant.

  Proof structure: pre-state case analysis on the value of `state` (one of
  four). For each pre-state, the Update CASE reduces to at most three
  outcomes for `state'`; in every outcome we either inherit peak_observed
  monotonicity from the inductive hypothesis or arm 1 of Update gives us
  new_peak = TRUE directly.

  Everything below is proved parametrically over Threshold, AwakenThreshold,
  Window and MaxDelta: the only premises are the four type ASSUMEs, and no
  constant is bound to a value anywhere in this module.

  controls/ConvergenceGovernorPhaseAware_NEG_ConvergenceRequiresHistory
  removes the peak-history guard and reaches a COOLING state without an
  observed peak. The remaining semantic obligations have corresponding
  controls in the same directory.
 ***************************************************************************)
EXTENDS ConvergenceGovernorPhaseAware, Naturals, Sequences, TLAPS

ASSUME ThresholdType        == Threshold \in Nat
ASSUME AwakenThresholdType  == AwakenThreshold \in Nat
ASSUME WindowType           == Window \in Nat /\ Window > 0
ASSUME MaxDeltaType         == MaxDelta \in Nat

\* ---- Inductive invariant -------------------------------------------------

WarmStateRequiresPeak ==
    state \in {"COOLING", "CONVERGED", "AWAKENED"} => peak_observed = TRUE

Inv ==
    /\ state \in GovernorStates
    /\ gradient_phase \in GradientPhases
    /\ delta_history \in Seq(0..MaxDelta)
    /\ Len(delta_history) <= Window
    /\ peak_observed \in BOOLEAN
    /\ NoCoolingFromCold
    /\ WarmStateRequiresPeak

\* ---- Helper lemma: ClassifyPhase is well-typed --------------------------

LEMMA ClassifyPhaseType ==
    ASSUME peak_observed \in BOOLEAN, NEW d \in Nat
    PROVE  ClassifyPhase(d) \in GradientPhases
  <1>1. CASE ~peak_observed /\ d < Threshold
    <2>1. ClassifyPhase(d) = "COLD"
      BY <1>1, ThresholdType DEF ClassifyPhase
    <2> QED                                 BY <2>1 DEF GradientPhases
  <1>2. CASE ~peak_observed /\ d >= Threshold
    <2>1. ClassifyPhase(d) = "WARMING"
      BY <1>2, ThresholdType DEF ClassifyPhase
    <2> QED                                 BY <2>1 DEF GradientPhases
  <1>3. CASE peak_observed /\ d >= Threshold
    <2>1. ClassifyPhase(d) = "ACTIVE_LEARNING"
      BY <1>3, ThresholdType DEF ClassifyPhase
    <2> QED                                 BY <2>1 DEF GradientPhases
  <1>4. CASE peak_observed /\ d < Threshold
    <2>1. ClassifyPhase(d) = "DECLINING"
      BY <1>4, ThresholdType DEF ClassifyPhase
    <2> QED                                 BY <2>1 DEF GradientPhases
  <1>5. d < Threshold \/ d >= Threshold     BY ThresholdType
  <1> QED                                   BY <1>1, <1>2, <1>3, <1>4, <1>5

\* ---- Helper lemma: ClassifyPhase /= "COLD" under positive peak signal ----

LEMMA ClassifyPhaseNotCold ==
    ASSUME peak_observed \in BOOLEAN, NEW d \in Nat,
           peak_observed \/ d >= Threshold
    PROVE  ClassifyPhase(d) /= "COLD"
  <1>1. CASE peak_observed /\ d >= Threshold
    BY <1>1, ThresholdType DEF ClassifyPhase
  <1>2. CASE peak_observed /\ d < Threshold
    BY <1>2, ThresholdType DEF ClassifyPhase
  <1>3. CASE ~peak_observed /\ d >= Threshold
    BY <1>3, ThresholdType DEF ClassifyPhase
  <1>4. d < Threshold \/ d >= Threshold     BY ThresholdType
  <1> QED                                    BY <1>1, <1>2, <1>3, <1>4

\* ---- Helper lemma: new history is bounded -------------------------------

NewHistory(d) ==
    IF Len(delta_history) >= Window
    THEN Append(Tail(delta_history), d)
    ELSE Append(delta_history, d)

LEMMA NewHistoryBounded ==
    ASSUME delta_history \in Seq(0..MaxDelta),
           Len(delta_history) <= Window,
           NEW d \in 0..MaxDelta
    PROVE  /\ NewHistory(d) \in Seq(0..MaxDelta)
           /\ Len(NewHistory(d)) <= Window
  <1>1. CASE Len(delta_history) >= Window
    <2>1. Len(delta_history) = Window
      BY <1>1, WindowType
    <2>2. Tail(delta_history) \in Seq(0..MaxDelta)
      BY <2>1, WindowType
    <2>3. Len(Tail(delta_history)) = Window - 1
      BY <2>1, WindowType
    <2>4. NewHistory(d) = Append(Tail(delta_history), d)
      BY <1>1 DEF NewHistory
    <2>5. NewHistory(d) \in Seq(0..MaxDelta)
      BY <2>2, <2>4
    <2>6. Len(NewHistory(d)) = Window
      BY <2>3, <2>4, WindowType
    <2> QED                                 BY <2>5, <2>6, WindowType
  <1>2. CASE Len(delta_history) < Window
    <2>0. ~(Len(delta_history) >= Window)
      BY <1>2, WindowType
    <2>1. NewHistory(d) = Append(delta_history, d)
      BY <2>0 DEF NewHistory
    <2>2. NewHistory(d) \in Seq(0..MaxDelta)
      BY <2>1
    <2>3. Len(NewHistory(d)) = Len(delta_history) + 1
      BY <2>1
    <2>4. Len(NewHistory(d)) <= Window
      BY <1>2, <2>3, WindowType
    <2> QED                                 BY <2>2, <2>4
  <1>3. Len(delta_history) >= Window \/ Len(delta_history) < Window
    BY WindowType
  <1> QED                                   BY <1>1, <1>2, <1>3

\* ---- Init lemma ----------------------------------------------------------

LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv             OBVIOUS
  <1>1. state \in GovernorStates                   BY DEF Init, GovernorStates
  <1>2. gradient_phase \in GradientPhases          BY DEF Init, GradientPhases
  <1>3. delta_history \in Seq(0..MaxDelta)         BY DEF Init
  <1>4. Len(delta_history) <= Window               BY WindowType DEF Init
  <1>5. peak_observed \in BOOLEAN                  BY DEF Init
  <1>6. NoCoolingFromCold                          BY DEF Init, NoCoolingFromCold
  <1>7. WarmStateRequiresPeak                      BY DEF Init, WarmStateRequiresPeak
  <1> QED   BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7 DEF Inv

\* ---- Next lemma ----------------------------------------------------------

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'    OBVIOUS
  <1>1. CASE UNCHANGED vars
    BY <1>1 DEF Inv, vars, NoCoolingFromCold, WarmStateRequiresPeak
  <1>2. CASE Next
    <2> SUFFICES ASSUME NEW d \in 0..MaxDelta, Update(d) PROVE Inv'
      BY <1>2 DEF Next
    \* Pre-state facts from Inv.
    <2>a. state \in GovernorStates                  BY DEF Inv
    <2>b. gradient_phase \in GradientPhases         BY DEF Inv
    <2>c. delta_history \in Seq(0..MaxDelta)        BY DEF Inv
    <2>d. Len(delta_history) <= Window              BY DEF Inv
    <2>e. peak_observed \in BOOLEAN                 BY DEF Inv
    <2>f. NoCoolingFromCold                         BY DEF Inv
    <2>g. WarmStateRequiresPeak                     BY DEF Inv
    <2>h. d \in Nat                                  BY MaxDeltaType
    \* Local name for the new history (= NewHistory(d) since vars match).
    <2>i. delta_history' = NewHistory(d)
      BY DEF Update, NewHistory
    <2>j. gradient_phase' = ClassifyPhase(d)
      BY DEF Update
    <2>k. peak_observed' = (peak_observed \/ d >= Threshold)
      BY DEF Update
    <2>l. peak_observed' \in BOOLEAN
      BY <2>e, <2>k
    \* Type components.
    <2>1. gradient_phase' \in GradientPhases
      BY <2>e, <2>h, <2>j, ClassifyPhaseType
    <2>2. delta_history' \in Seq(0..MaxDelta) /\ Len(delta_history') <= Window
      BY <2>c, <2>d, <2>i, NewHistoryBounded
    <2>3. peak_observed' \in BOOLEAN
      BY <2>l
    \* state' \in GovernorStates, with the case-analysis facts it rests on.
    <2>4. state' \in GovernorStates
      <3>1. CASE state = "ACTIVE"
        BY <2>a, <2>e, <3>1, ThresholdType DEF Update, GovernorStates
      <3>2. CASE state = "COOLING"
        BY <2>a, <3>2, ThresholdType DEF Update, GovernorStates
      <3>3. CASE state = "CONVERGED"
        BY <2>a, <3>3, AwakenThresholdType DEF Update, GovernorStates
      <3>4. CASE state = "AWAKENED"
        BY <2>a, <3>4, ThresholdType DEF Update, GovernorStates
      <3> QED  BY <2>a, <3>1, <3>2, <3>3, <3>4 DEF GovernorStates
    \* WarmStateRequiresPeak'.
    <2>5. WarmStateRequiresPeak'
      <3> SUFFICES ASSUME state' \in {"COOLING", "CONVERGED", "AWAKENED"}
                   PROVE  peak_observed' = TRUE
        BY DEF WarmStateRequiresPeak
      \* Pre-state case analysis on `state`. In every case where state' is
      \* in the warm set, either peak_observed was TRUE (so peak_observed'
      \* is TRUE by monotonicity) or arm 1 of Update fires (state = ACTIVE,
      \* state' = COOLING) which requires new_peak = TRUE directly.
      <3>1. CASE state \in {"COOLING", "CONVERGED", "AWAKENED"}
        \* Warm pre-state: peak_observed = TRUE by IH; new_peak inherits.
        <4>1. peak_observed = TRUE
          BY <2>g, <3>1 DEF WarmStateRequiresPeak
        <4>2. peak_observed' = TRUE
          BY <2>e, <2>k, <4>1
        <4> QED  BY <4>2
      <3>2. CASE state = "ACTIVE"
        \* Cold pre-state. state' \in {"ACTIVE", "COOLING"} only.
        \* By the sufficient hypothesis, state' is in the warm set, so
        \* state' = "COOLING". Arm 1 of Update fires, requiring new_peak.
        <4>1. state' = "COOLING"
          BY <2>a, <2>e, <3>2, ThresholdType DEF Update, GovernorStates
        <4>2. peak_observed \/ d >= Threshold
          BY <2>a, <2>e, <3>2, <4>1, ThresholdType DEF Update, GovernorStates
        <4>3. peak_observed' = TRUE
          BY <2>e, <2>k, <4>2
        <4> QED  BY <4>3
      <3> QED  BY <2>a, <3>1, <3>2 DEF GovernorStates
    \* NoCoolingFromCold'.
    <2>6. NoCoolingFromCold'
      <3> SUFFICES ASSUME state' = "COOLING"
                   PROVE  gradient_phase' /= "COLD"
        BY DEF NoCoolingFromCold
      \* Pre-state case analysis on `state`. state' = "COOLING" comes from
      \* either ACTIVE (arm 1: requires new_peak) or COOLING (other-arm,
      \* peak_observed TRUE by IH).
      <3>1. CASE state = "ACTIVE"
        \* Arm 1: avg < Threshold * 2 /\ new_peak.
        <4>1. peak_observed \/ d >= Threshold
          BY <2>a, <2>e, <3>1, ThresholdType DEF Update, GovernorStates
        <4>2. ClassifyPhase(d) /= "COLD"
          BY <2>e, <2>h, <4>1, ClassifyPhaseNotCold
        <4> QED  BY <2>j, <4>2
      <3>2. CASE state = "COOLING"
        \* peak_observed = TRUE by IH.
        <4>1. peak_observed = TRUE
          BY <2>g, <3>2 DEF WarmStateRequiresPeak
        <4>2. peak_observed \/ d >= Threshold
          BY <4>1
        <4>3. ClassifyPhase(d) /= "COLD"
          BY <2>e, <2>h, <4>2, ClassifyPhaseNotCold
        <4> QED  BY <2>j, <4>3
      <3>3. CASE state \in {"CONVERGED", "AWAKENED"}
        \* From CONVERGED: state' \in {CONVERGED, AWAKENED}, not COOLING.
        \* From AWAKENED: state' \in {AWAKENED, CONVERGED}, not COOLING.
        \* So state' /= "COOLING", contradicting the SUFFICES assumption.
        <4>1. state' /= "COOLING"
          BY <2>a, <3>3, AwakenThresholdType, ThresholdType DEF Update, GovernorStates
        <4> QED  BY <4>1
      <3> QED  BY <2>a, <3>1, <3>2, <3>3 DEF GovernorStates
    <2> QED  BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6
             DEF Inv, NoCoolingFromCold, WarmStateRequiresPeak
  <1> QED   BY <1>1, <1>2

\* ---- Main safety theorems -----------------------------------------------

THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv               BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'  BY NextInv
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

THEOREM TypeSafety == Spec => []TypeInvariant
  <1>1. Inv => TypeInvariant       BY DEF Inv, TypeInvariant
  <1> QED  BY Safety, <1>1, PTL

THEOREM NoCoolingFromColdSafety == Spec => []NoCoolingFromCold
  <1>1. Inv => NoCoolingFromCold   BY DEF Inv
  <1> QED  BY Safety, <1>1, PTL

THEOREM ConvergenceRequiresHistorySafety == Spec => []ConvergenceRequiresHistory
  <1>1. Inv => ConvergenceRequiresHistory
    BY DEF Inv, WarmStateRequiresPeak, ConvergenceRequiresHistory
  <1> QED  BY Safety, <1>1, PTL

LEMMA ConvergedRequiresPeakDerivedProof ==
    ConvergenceRequiresHistory => ConvergedRequiresPeak
  BY DEF ConvergenceRequiresHistory, ConvergedRequiresPeak

THEOREM ConvergedRequiresPeakSafety == Spec => []ConvergedRequiresPeak
  BY ConvergenceRequiresHistorySafety, ConvergedRequiresPeakDerivedProof, PTL

THEOREM SafetyOriginal ==
    Spec => [](NoCoolingFromCold /\ ConvergenceRequiresHistory)
  <1>1. Inv => NoCoolingFromCold /\ ConvergenceRequiresHistory
    BY DEF Inv, WarmStateRequiresPeak, ConvergenceRequiresHistory
  <1> QED  BY Safety, <1>1, PTL

\* ---- ValidTransitions: the governor steps only along the allowed graph -----
\* A two-state (action) property.  The step lemma evaluates the Update CASE per
\* pre-state; ValidTransitionsSafety lifts it to the temporal PROPERTY
\* ValidTransitionsProp, which the .cfg checks.
LEMMA ValidTransitionsStep == Inv /\ [Next]_vars => ValidTransitions
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE ValidTransitions  OBVIOUS
  <1>1. CASE UNCHANGED vars
    BY <1>1 DEF vars, ValidTransitions
  <1>2. CASE Next
    <2> SUFFICES ASSUME NEW d \in 0..MaxDelta, Update(d) PROVE ValidTransitions
      BY <1>2 DEF Next
    <2>a. state \in GovernorStates   BY DEF Inv
    <2>e. peak_observed \in BOOLEAN   BY DEF Inv
    <2>1. state = "ACTIVE" => state' \in {"ACTIVE", "COOLING"}
      BY <2>a, <2>e, ThresholdType DEF Update, GovernorStates
    <2>2. state = "COOLING" => state' \in {"COOLING", "CONVERGED", "ACTIVE"}
      BY <2>a, ThresholdType DEF Update, GovernorStates
    <2>3. state = "CONVERGED" => state' \in {"CONVERGED", "AWAKENED"}
      BY <2>a, AwakenThresholdType DEF Update, GovernorStates
    <2>4. state = "AWAKENED" => state' \in {"AWAKENED", "CONVERGED"}
      BY <2>a, ThresholdType DEF Update, GovernorStates
    <2> QED  BY <2>1, <2>2, <2>3, <2>4 DEF ValidTransitions
  <1> QED  BY <1>1, <1>2

THEOREM ValidTransitionsSafety == Spec => ValidTransitionsProp
  <1>1. Inv /\ [Next]_vars => [ValidTransitions]_vars
    BY ValidTransitionsStep
  <1>2. Spec => []Inv  BY Safety
  <1> QED  BY <1>1, <1>2, PTL DEF Spec, ValidTransitionsProp

====
