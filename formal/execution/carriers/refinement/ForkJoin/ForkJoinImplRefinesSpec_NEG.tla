---- MODULE ForkJoinImplRefinesSpec_NEG ----
(***************************************************************************)
(* A faulty start changes two ready workers in one commit. The state stays  *)
(* typed, but no canonical one-worker StartWorker action matches the step.  *)
(***************************************************************************)
\* EXPECT: VIOLATION
EXTENDS ForkJoinImplRefinesSpec

AdjacentInvariant == TypeInvariant

FaultStartTwo ==
    \E a, b \in Workers :
        /\ a # b
        /\ phase = "fork"
        /\ wstate[a] = "ready"
        /\ wstate[b] = "ready"
        /\ wstate' = [[wstate EXCEPT ![a] = "running"] EXCEPT ![b] = "running"]
        /\ UNCHANGED <<wvalue, phase, output_ready, output_snapshot>>
        /\ AdjacentInvariant'

FaultNext == FaultStartTwo \/ ImplNext
FaultRefinement == Refinement
====

