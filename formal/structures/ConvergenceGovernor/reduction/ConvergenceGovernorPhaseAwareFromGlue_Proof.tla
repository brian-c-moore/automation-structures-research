---- MODULE ConvergenceGovernorPhaseAwareFromGlue_Proof ----
(***************************************************************************
  Parametric TLAPS proof of the ConvergenceGovernorPhaseAware pure-glue
  refinement:

      Refinement == Spec => CG!Spec

  Under the substitution, Init, Next, and vars are the phase-aware carrier with
  renamed variables. Threshold, awaken-threshold, window, and delta typing are
  used for the construction TypeInvariant. The proof does not show that a
  retained component supplies the governor safety or transition obligations;
  their state remains glue.
 ***************************************************************************)
EXTENDS ConvergenceGovernorPhaseAwareFromGlue, TLAPS

ASSUME ThresholdType       == Threshold \in Nat
ASSUME AwakenThresholdType == AwakenThreshold \in Nat
ASSUME WindowType          == Window \in Nat /\ Window > 0
ASSUME MaxDeltaType        == MaxDelta \in Nat

\* Inductive strengthening. TypeInvariant bounds the window's LENGTH but does
\* not say the window is a sequence of deltas, and the Tail/Append arithmetic
\* of the sliding rule needs that.
Inv ==
    /\ g_state \in GovernorStates
    /\ g_phase \in GradientPhases
    /\ g_history \in Seq(0..MaxDelta)
    /\ Len(g_history) <= Window
    /\ g_peak \in BOOLEAN

(*-------------------------------------------------------------------------*)
(* Helper: the phase classifier is total into the four phases.             *)
(*-------------------------------------------------------------------------*)
LEMMA ClassifyPhaseType ==
    ASSUME g_peak \in BOOLEAN, NEW d \in Nat
    PROVE  ClassifyPhase(d) \in GradientPhases
  <1>1. CASE ~g_peak /\ d < Threshold
    <2>1. ClassifyPhase(d) = "COLD"
      BY <1>1, ThresholdType DEF ClassifyPhase
    <2> QED                                 BY <2>1 DEF GradientPhases
  <1>2. CASE ~g_peak /\ d >= Threshold
    <2>1. ClassifyPhase(d) = "WARMING"
      BY <1>2, ThresholdType DEF ClassifyPhase
    <2> QED                                 BY <2>1 DEF GradientPhases
  <1>3. CASE g_peak /\ d >= Threshold
    <2>1. ClassifyPhase(d) = "ACTIVE_LEARNING"
      BY <1>3, ThresholdType DEF ClassifyPhase
    <2> QED                                 BY <2>1 DEF GradientPhases
  <1>4. CASE g_peak /\ d < Threshold
    <2>1. ClassifyPhase(d) = "DECLINING"
      BY <1>4, ThresholdType DEF ClassifyPhase
    <2> QED                                 BY <2>1 DEF GradientPhases
  <1>5. d < Threshold \/ d >= Threshold     BY ThresholdType
  <1> QED                                   BY <1>1, <1>2, <1>3, <1>4, <1>5

(*-------------------------------------------------------------------------*)
(* Helper: the sliding window stays a bounded sequence of deltas.          *)
(*-------------------------------------------------------------------------*)
NewHistory(d) ==
    IF Len(g_history) >= Window
    THEN Append(Tail(g_history), d)
    ELSE Append(g_history, d)

LEMMA NewHistoryBounded ==
    ASSUME g_history \in Seq(0..MaxDelta),
           Len(g_history) <= Window,
           NEW d \in 0..MaxDelta
    PROVE  /\ NewHistory(d) \in Seq(0..MaxDelta)
           /\ Len(NewHistory(d)) <= Window
  <1>1. CASE Len(g_history) >= Window
    <2>1. Len(g_history) = Window
      BY <1>1, WindowType
    <2>2. Tail(g_history) \in Seq(0..MaxDelta)
      BY <2>1, WindowType
    <2>3. Len(Tail(g_history)) = Window - 1
      BY <2>1, WindowType
    <2>4. NewHistory(d) = Append(Tail(g_history), d)
      BY <1>1 DEF NewHistory
    <2>5. NewHistory(d) \in Seq(0..MaxDelta)
      BY <2>2, <2>4
    <2>6. Len(NewHistory(d)) = Window
      BY <2>3, <2>4, WindowType
    <2> QED                                 BY <2>5, <2>6, WindowType
  <1>2. CASE Len(g_history) < Window
    <2>0. ~(Len(g_history) >= Window)
      BY <1>2, WindowType
    <2>1. NewHistory(d) = Append(g_history, d)
      BY <2>0 DEF NewHistory
    <2>2. NewHistory(d) \in Seq(0..MaxDelta)
      BY <2>1
    <2>3. Len(NewHistory(d)) = Len(g_history) + 1
      BY <2>1
    <2>4. Len(NewHistory(d)) <= Window
      BY <1>2, <2>3, WindowType
    <2> QED                                 BY <2>2, <2>4
  <1>3. Len(g_history) >= Window \/ Len(g_history) < Window
    BY WindowType
  <1> QED                                   BY <1>1, <1>2, <1>3

(*-------------------------------------------------------------------------*)
(* Safety of the construction's own (type) invariant.                      *)
(*-------------------------------------------------------------------------*)
LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv             OBVIOUS
  <1>1. g_state \in GovernorStates                 BY DEF Init, GovernorStates
  <1>2. g_phase \in GradientPhases                 BY DEF Init, GradientPhases
  <1>3. g_history \in Seq(0..MaxDelta)             BY DEF Init
  <1>4. Len(g_history) <= Window                   BY WindowType DEF Init
  <1>5. g_peak \in BOOLEAN                         BY DEF Init
  <1> QED  BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF Inv

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'    OBVIOUS
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF Inv, vars
  <1>X. CASE Next
    <2> SUFFICES ASSUME NEW d \in 0..MaxDelta, Update(d) PROVE Inv'
      BY <1>X DEF Next
    <2>a. g_state \in GovernorStates                 BY DEF Inv
    <2>c. g_history \in Seq(0..MaxDelta)             BY DEF Inv
    <2>d. Len(g_history) <= Window                   BY DEF Inv
    <2>e. g_peak \in BOOLEAN                         BY DEF Inv
    <2>h. d \in Nat                                   BY MaxDeltaType
    <2>i. g_history' = NewHistory(d)
      BY DEF Update, NewHistory
    <2>j. g_phase' = ClassifyPhase(d)
      BY DEF Update
    <2>k. g_peak' = (g_peak \/ d >= Threshold)
      BY DEF Update
    <2>1. g_phase' \in GradientPhases
      BY <2>e, <2>h, <2>j, ClassifyPhaseType
    <2>2. g_history' \in Seq(0..MaxDelta) /\ Len(g_history') <= Window
      BY <2>c, <2>d, <2>i, NewHistoryBounded
    <2>3. g_peak' \in BOOLEAN
      BY <2>e, <2>k
    <2>4. g_state' \in GovernorStates
      <3>1. CASE g_state = "ACTIVE"
        BY <2>a, <2>e, <3>1, ThresholdType DEF Update, GovernorStates
      <3>2. CASE g_state = "COOLING"
        BY <2>a, <3>2, ThresholdType DEF Update, GovernorStates
      <3>3. CASE g_state = "CONVERGED"
        BY <2>a, <3>3, AwakenThresholdType DEF Update, GovernorStates
      <3>4. CASE g_state = "AWAKENED"
        BY <2>a, <3>4, ThresholdType DEF Update, GovernorStates
      <3> QED  BY <2>a, <3>1, <3>2, <3>3, <3>4 DEF GovernorStates
    <2> QED  BY <2>1, <2>2, <2>3, <2>4 DEF Inv
  <1> QED   BY <1>0, <1>X

THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv                    BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'     BY NextInv
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

\* The construction's .cfg-checked invariant, now unbounded.
THEOREM TypeSafety == Spec => []TypeInvariant
  <1>1. Inv => TypeInvariant
    BY DEF Inv, TypeInvariant
  <1> QED  BY Safety, <1>1, PTL

(*-------------------------------------------------------------------------*)
(* The refinement. No invariant is carried into it and none is needed: the  *)
(* substitution is a relabelling, so the step below is the carrier's own    *)
(* Update read under the new variable names.                                *)
(*-------------------------------------------------------------------------*)
LEMMA InitRefines == Init => CG!Init
  BY DEF Init, CG!Init

LEMMA NextRefines == [Next]_vars => [CG!Next]_(CG!vars)
  <1> SUFFICES ASSUME [Next]_vars PROVE [CG!Next]_(CG!vars)
    OBVIOUS
  <1>0. CASE UNCHANGED vars
    <2>1. UNCHANGED <<g_state, g_phase, g_history, g_peak>>
      BY <1>0 DEF vars
    <2> QED  BY <2>1 DEF CG!vars
  <1>X. CASE Next
    <2> SUFFICES ASSUME NEW d \in 0..MaxDelta, Update(d)
                 PROVE  CG!Next
      BY <1>X DEF Next
    <2>1. CG!Update(d)
      BY DEF Update, CG!Update, ClassifyPhase, CG!ClassifyPhase,
             SumSeq, CG!SumSeq, Max, CG!Max
    <2> QED  BY <2>1 DEF CG!Next
  <1> QED  BY <1>0, <1>X

(*-------------------------------------------------------------------------*)
(* The main result is an unbounded refinement under direct state relabeling. *)
(* It does not transfer the governor obligations from another component.    *)
(*-------------------------------------------------------------------------*)
THEOREM Refinement == Spec => CG!Spec
  <1>1. Init => CG!Init                                 BY InitRefines
  <1>2. [Next]_vars => [CG!Next]_(CG!vars)              BY NextRefines
  <1> QED  BY <1>1, <1>2, PTL DEF Spec, CG!Spec

\* Restatement in the base module's own vocabulary.
THEOREM RefinementOriginal == Spec => ConvergenceGovernorRefinement
  BY Refinement DEF ConvergenceGovernorRefinement

====
