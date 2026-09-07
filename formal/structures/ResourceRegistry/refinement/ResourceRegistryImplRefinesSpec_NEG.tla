---- MODULE ResourceRegistryImplRefinesSpec_NEG ----
(***************************************************************************)
(* Isolated upsert fault: the old pair is retained before the replacement  *)
(* pair is inserted. Pair typing remains checked; UniqueMapping and the     *)
(* canonical Register relation are the named failing seams.                 *)
(***************************************************************************)
\* EXPECT: VIOLATION
EXTENDS ResourceRegistryImplRefinesSpec

AdjacentInvariant == TypeInvariant

FaultRegister(k, v) ==
    /\ AdjacentInvariant
    /\ k \in Keys
    /\ v \in Values
    /\ \E old \in Values : old /= v /\ <<k, old>> \in entries
    /\ entries' = entries \cup {<<k, v>>}
    /\ AdjacentInvariant'

FaultNext ==
    \/ \E k \in Keys, v \in Values : ImplRegister(k, v)
    \/ \E k \in Keys, v \in Values : FaultRegister(k, v)
    \/ \E k \in Keys : ImplDeregister(k)
    \/ ImplReadOrReject

FaultRefinement == R!Spec
====
