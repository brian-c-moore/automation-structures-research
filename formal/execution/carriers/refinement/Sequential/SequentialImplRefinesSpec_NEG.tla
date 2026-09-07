---- MODULE SequentialImplRefinesSpec_NEG ----
(***************************************************************************)
(* A faulty completion advances the cursor without appending to history.   *)
(* The state remains typed, but no canonical Sequential action matches it. *)
(***************************************************************************)
\* EXPECT: VIOLATION
EXTENDS SequentialImplRefinesSpec

AdjacentInvariant ==
    /\ pc \in 0..Steps
    /\ value \in ValueDomain
    /\ active \in BOOLEAN
    /\ history \in Seq(ValueDomain)

FaultCompleteStep ==
    /\ active
    /\ pc < Steps
    /\ pc' = pc + 1
    /\ active' = FALSE
    /\ UNCHANGED <<value, history>>
    /\ AdjacentInvariant'

FaultNext == ImplBeginStep \/ FaultCompleteStep \/ ImplDoneStuttering
FaultRefinement == Refinement
====

