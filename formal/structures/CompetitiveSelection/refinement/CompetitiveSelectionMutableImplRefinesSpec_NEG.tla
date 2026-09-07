---- MODULE CompetitiveSelectionMutableImplRefinesSpec_NEG ----
(***************************************************************************)
(* Mutable-score fault: one writer changes two candidates while resetting  *)
(* the partial awards. The reset preserves every adjacent invariant, but   *)
(* the canonical UpdateScore action changes exactly one candidate.          *)
(***************************************************************************)
\* EXPECT: VIOLATION
EXTENDS CompetitiveSelectionImplRefinesSpec

AdjacentInvariant == ImplInvariant
FaultMutableMultiUpdate ==
    /\ AdjacentInvariant
    /\ mutable_scores[0] = 1
    /\ mutable_scores[1] = 2
    /\ mutable_scores' = [mutable_scores EXCEPT ![0] = 2, ![1] = 1]
    /\ mutable_extra' = [c \in Candidates |-> 0]
    /\ UNCHANGED <<hard_vars, soft_vars,
                    mutable_weight_total, mutable_max_score, ranked_vars>>
    /\ AdjacentInvariant'

FaultNext == MutableStep \/ FaultMutableMultiUpdate \/ ImplRead
MutableFaultRefinement == MS!MutableScoreSpec
====
