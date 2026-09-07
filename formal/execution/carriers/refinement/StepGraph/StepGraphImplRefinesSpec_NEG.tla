---- MODULE StepGraphImplRefinesSpec_NEG ----
(***************************************************************************)
(* A faulty start jumps directly from Ready to Completed. Eligibility and  *)
(* typing remain intact, but no canonical one-rank action matches the step. *)
(***************************************************************************)
\* EXPECT: VIOLATION
EXTENDS StepGraphImplRefinesSpec

AdjacentInvariant == ImplInvariant

FaultStartRunning(n) ==
    /\ n \in Nodes
    /\ nstate[n] = "Ready"
    /\ nstate' = [nstate EXCEPT ![n] = "Completed"]
    /\ AdjacentInvariant'

FaultNext == (\E n \in Nodes : FaultStartRunning(n)) \/ ImplNext
FaultRefinement == Refinement
====

