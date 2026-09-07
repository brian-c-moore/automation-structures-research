---- MODULE BisectionImplRefinesSpec_NEG ----
(***************************************************************************)
(* Isolated endpoint fault: a left probe moves both endpoints. Typing,      *)
(* monotonicity, the probe bound, and the width bound remain true; exact    *)
(* midpoint action correspondence fails.                                   *)
(***************************************************************************)
\* EXPECT: VIOLATION
EXTENDS BisectionImplRefinesSpec

AdjacentInvariant == ImplInvariant
FaultProbeLeft ==
    /\ AdjacentInvariant
    /\ hi - lo >= 2
    /\ Mid >= threshold
    /\ lo + 1 <= threshold
    /\ hi' = Mid
    /\ lo' = lo + 1
    /\ probes_taken' = probes_taken + 1
    /\ UNCHANGED <<domain_size, threshold, max_probes>>
    /\ AdjacentInvariant'

FaultNext == FaultProbeLeft \/ ImplProgress \/ ImplReadOrConverged
FaultRefinement == SafetyRefinement
====
