---- MODULE ResourceRegistryImplRefinesSpec ----
(***************************************************************************)
(* Contract transcription for ResourceRegistry. Source:                   *)
(* crate://automation-structures/0.2.3/src/primitives/resource_registry.rs.        *)
(*                                                                         *)
(* The mutable Vec<(u64,u64)> maps to the set of its pairs. Sequence order  *)
(* is a hidden representation detail. contains_key and maps_to are          *)
(* read-only projections. register and deregister contracts determine the   *)
(* projected set exactly; rejected deregistration and queries stutter.      *)
(***************************************************************************)
\* EXPECT: OK
EXTENDS Naturals, FiniteSets

CONSTANTS MaxKey, MaxValue
ASSUME MaxKeyType == MaxKey \in Nat
ASSUME MaxValueType == MaxValue \in Nat

Keys == 0..MaxKey
Values == 0..MaxValue

VARIABLE entries
vars == <<entries>>

TypeInvariant == entries \subseteq (Keys \X Values)
UniqueMapping ==
    \A k \in Keys : Cardinality({v \in Values : <<k, v>> \in entries}) <= 1
ImplInvariant == TypeInvariant /\ UniqueMapping

Init == entries = {} /\ ImplInvariant

ImplRegister(k, v) ==
    /\ ImplInvariant
    /\ k \in Keys
    /\ v \in Values
    /\ entries' = {e \in entries : e[1] /= k} \cup {<<k, v>>}
    /\ ImplInvariant'

ImplDeregister(k) ==
    /\ ImplInvariant
    /\ k \in Keys
    /\ \E v \in Values : <<k, v>> \in entries
    /\ entries' = {e \in entries : e[1] /= k}
    /\ ImplInvariant'

ImplReadOrReject == UNCHANGED vars

ImplNext ==
    \/ \E k \in Keys, v \in Values : ImplRegister(k, v)
    \/ \E k \in Keys : ImplDeregister(k)
    \/ ImplReadOrReject

Spec == Init /\ [][ImplNext]_vars

R == INSTANCE ResourceRegistry WITH
        Keys <- Keys,
        Values <- Values,
        entries <- entries

Refinement == R!Spec
====
