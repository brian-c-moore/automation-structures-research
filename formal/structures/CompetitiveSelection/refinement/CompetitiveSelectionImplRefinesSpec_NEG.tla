---- MODULE CompetitiveSelectionImplRefinesSpec_NEG ----
(***************************************************************************)
(* Shared-state fault: a hard score update clears only the changed seat.    *)
(* The other seat remains a valid unique optimum in this witness, so all   *)
(* adjacent hard invariants remain true. Canonical UpdateScore clears the   *)
(* whole coupled assignment.                                                *)
(***************************************************************************)
\* EXPECT: VIOLATION
EXTENDS CompetitiveSelectionImplRefinesSpec

AdjacentInvariant == ImplInvariant
FaultHardUpdate ==
    /\ AdjacentInvariant
    /\ hard_allocation[0] = 0
    /\ hard_allocation[1] = 1
    /\ hard_scores[1][1] > hard_scores[1][0]
    /\ hard_scores' = [hard_scores EXCEPT ![0][0] = 1]
    /\ hard_allocation' = [hard_allocation EXCEPT ![0] = NullValue]
    /\ UNCHANGED <<hard_num_seats, hard_num_candidates, hard_max_score,
                    soft_vars, mutable_vars, ranked_vars>>
    /\ AdjacentInvariant'

FaultNext ==
    \/ HardStep
    \/ FaultHardUpdate
    \/ ImplRead
HardFaultRefinement == H!Spec
====
