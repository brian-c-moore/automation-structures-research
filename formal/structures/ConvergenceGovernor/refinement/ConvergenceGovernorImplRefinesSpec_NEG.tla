---- MODULE ConvergenceGovernorImplRefinesSpec_NEG ----
(***************************************************************************)
(* Isolated phase-classification fault: a cold zero delta is labeled        *)
(* WARMING. All adjacent state invariants remain true; Update fidelity      *)
(* fails.                                                                   *)
(***************************************************************************)
\* EXPECT: VIOLATION
EXTENDS ConvergenceGovernorImplRefinesSpec

AdjacentInvariant == ImplInvariant
FaultUpdate ==
    /\ AdjacentInvariant
    /\ state = "ACTIVE"
    /\ peak_observed = FALSE
    /\ 0 < threshold
    /\ delta_history' = NewHistory(delta_history, 0)
    /\ gradient_phase' = "WARMING"
    /\ peak_observed' = FALSE
    /\ state' = "ACTIVE"
    /\ UNCHANGED <<threshold, awaken_threshold, window, max_delta>>
    /\ AdjacentInvariant'

FaultNext == FaultUpdate \/ (\E d \in 0..MaxDelta : ImplUpdate(d)) \/ ImplRead
FaultRefinement == C!Spec
====
