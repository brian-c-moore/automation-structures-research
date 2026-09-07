---- MODULE ActuationPassImplRefinesSpec_NEG ----
(***************************************************************************)
(* Isolated mapping fault: FaultActuate records FaultResource instead of   *)
(* the resource read from allocation. Typing, ActuationScope, and          *)
(* PassCompleteness remain checked. EffectFidelity is the named seam.       *)
(***************************************************************************)
\* EXPECT: VIOLATION
EXTENDS ActuationPassImplRefinesSpec

CONSTANT FaultResource
ASSUME FaultResourceType == FaultResource \in ResourceDomain

AdjacentInvariant == TypeInvariant /\ ActuationScope /\ PassCompleteness

FaultActuate(s) ==
    /\ AdjacentInvariant
    /\ s \in Seats
    /\ ~complete
    /\ effects[s] = NullValue
    /\ allocation[s] /= NullValue
    /\ allocation[s] /= FaultResource
    /\ effects' = [effects EXCEPT ![s] = FaultResource]
    /\ UNCHANGED <<num_seats, allocation, complete>>
    /\ AdjacentInvariant'

FaultNext ==
    \/ \E s \in Seats, r \in ResourceDomain : ImplAllocate(s, r)
    \/ \E s \in Seats : ImplDeallocate(s)
    \/ \E s \in Seats : FaultActuate(s)
    \/ ImplFinish
    \/ ImplReadOrReject

FaultRefinement == A!Spec
====
