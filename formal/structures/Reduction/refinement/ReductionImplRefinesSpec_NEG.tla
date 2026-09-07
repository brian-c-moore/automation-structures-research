---- MODULE ReductionImplRefinesSpec_NEG ----
(***************************************************************************)
(* Isolated multiplicity fault: consume two source elements in one commit. *)
(* Partition and exact consumed-prefix fold remain true, but one canonical  *)
(* Consume action advances the position by exactly one.                     *)
(***************************************************************************)
\* EXPECT: VIOLATION
EXTENDS ReductionImplRefinesSpec

AdjacentInvariant == ImplInvariant
FaultConsumeTwo ==
    /\ AdjacentInvariant
    /\ Len(remaining) >= 2
    /\ processed' =
        Append(Append(processed, Head(remaining)), Head(Tail(remaining)))
    /\ remaining' = Tail(Tail(remaining))
    /\ result' = result + Head(remaining) + Head(Tail(remaining))
    /\ pos' = pos + 2
    /\ UNCHANGED original
    /\ AdjacentInvariant'

FaultNext == FaultConsumeTwo \/ ImplProcess \/ ImplReadOrDone
FaultRefinement == R!Spec
====
