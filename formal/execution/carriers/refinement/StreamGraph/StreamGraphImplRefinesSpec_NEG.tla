---- MODULE StreamGraphImplRefinesSpec_NEG ----
(***************************************************************************)
(* A faulty ingest appends one record but advances the input count twice.   *)
(* The state remains typed, but no canonical ingest action matches it.      *)
(***************************************************************************)
\* EXPECT: VIOLATION
EXTENDS StreamGraphImplRefinesSpec

AdjacentInvariant == TypeInvariant

FaultSourceIngest(v) ==
    /\ ingested + 2 <= MaxInputs
    /\ ~IsFull(q1)
    /\ v \in RecordDomain
    /\ q1' = Append(q1, v)
    /\ ingested' = ingested + 2
    /\ UNCHANGED <<q2, q3, emitted>>
    /\ AdjacentInvariant'

FaultNext == (\E v \in RecordDomain : FaultSourceIngest(v)) \/ ImplNext
FaultRefinement == Refinement
====

