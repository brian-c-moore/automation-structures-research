---- MODULE CompetitiveSelectionRankedUnderSelectionImplRefinesSpec_NEG ----
(***************************************************************************)
(* Ranked fault: return one ordered winner when K requires both candidates. *)
(* The adjacent bounded and ordering invariants remain true, but the exact   *)
(* selected-count clause and canonical Select relation both fail.           *)
(***************************************************************************)
\* EXPECT: VIOLATION
EXTENDS CompetitiveSelectionImplRefinesSpec

AdjacentInvariant == ImplInvariant
FaultRankedUnderSelection ==
    /\ AdjacentInvariant
    /\ ranked_selected = {}
    /\ ranked_scores = [c \in Candidates |-> IF c = 0 THEN 2 ELSE 1]
    /\ ranked_selected' = {0}
    /\ UNCHANGED <<hard_vars, soft_vars, mutable_vars,
                    ranked_k, ranked_max_score, ranked_scores>>
    /\ AdjacentInvariant'

FaultNext == RankedStep \/ FaultRankedUnderSelection \/ ImplRead
RankedUnderSelectionFaultRefinement == R!Spec
====
