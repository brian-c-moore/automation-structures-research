---- MODULE SamplerImplRefinesSpec_NEG ----
(***************************************************************************)
(* Isolated atomicity fault: publish two supported samples in one commit.  *)
(* BoundedSample and SupportConsistency remain true, but one canonical     *)
(* Sample action can add at most one item.                                  *)
(***************************************************************************)
\* EXPECT: VIOLATION
EXTENDS SamplerImplRefinesSpec

AdjacentInvariant == ImplInvariant
FaultSampleTwo ==
    /\ AdjacentInvariant
    /\ selected = {}
    /\ distribution[0] > 0
    /\ distribution[1] > 0
    /\ selected' = {0, 1}
    /\ UNCHANGED <<num_items, sample_size, distribution>>
    /\ AdjacentInvariant'

FaultNext == FaultSampleTwo \/ ImplReadOrReject
FaultRefinement == S!Spec
====
