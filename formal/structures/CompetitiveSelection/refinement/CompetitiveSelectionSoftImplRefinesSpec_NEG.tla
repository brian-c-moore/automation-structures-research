---- MODULE CompetitiveSelectionSoftImplRefinesSpec_NEG ----
(***************************************************************************)
(* Reserved-floor soft fault: erase a completed award without changing the *)
(* score vector. The adjacent soft invariants remain true after returning  *)
(* to the reserved floor, but AssignNext cannot remove an award.            *)
(***************************************************************************)
\* EXPECT: VIOLATION
EXTENDS CompetitiveSelectionImplRefinesSpec

AdjacentInvariant == ImplInvariant
FaultSoftReset ==
    /\ AdjacentInvariant
    /\ S!WSum[S!WN] > S!WN
    /\ soft_extra' = [c \in Candidates |-> 0]
    /\ soft_scores' = soft_scores
    /\ UNCHANGED <<hard_vars, soft_weight_total, soft_max_score,
                    mutable_vars, ranked_vars>>
    /\ AdjacentInvariant'

FaultNext == SoftStep \/ FaultSoftReset \/ ImplRead
SoftFaultRefinement == S!Spec
====
