---- MODULE CompetitiveSelectionRankedImplRefinesSpec_NEG ----
(***************************************************************************)
(* Ranked fault: improve a selected candidate without clearing selection.  *)
(* The ranked invariants remain true, but Select cannot change scores and  *)
(* UpdateScores must clear the selected set.                                *)
(***************************************************************************)
\* EXPECT: VIOLATION
EXTENDS CompetitiveSelectionImplRefinesSpec

AdjacentInvariant == ImplInvariant
FaultRankedScoreWithoutClear ==
    /\ AdjacentInvariant
    /\ \E s \in ranked_selected :
          /\ ranked_scores[s] < MaxScore
          /\ ranked_scores' = [ranked_scores EXCEPT ![s] = @ + 1]
          /\ ranked_selected' = ranked_selected
          /\ UNCHANGED <<hard_vars, soft_vars, mutable_vars,
                          ranked_k, ranked_max_score>>
          /\ AdjacentInvariant'

FaultNext == RankedStep \/ FaultRankedScoreWithoutClear \/ ImplRead
RankedFaultRefinement == R!Spec
====
