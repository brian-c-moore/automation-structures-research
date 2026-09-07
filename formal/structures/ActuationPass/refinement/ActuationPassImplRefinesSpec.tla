---- MODULE ActuationPassImplRefinesSpec ----
(***************************************************************************)
(* Contract-induced transition system for the Verus ActuationPass carrier. *)
(* Source: crate://automation-structures/0.2.3/src/primitives/actuation_pass.rs.    *)
(*                                                                         *)
(* Mutable and observable field map:                                       *)
(*   num_seats -> Cardinality(Seats), immutable representation field       *)
(*   allocation -> allocation, effects -> effects, complete -> complete    *)
(* Option::None maps to NullValue; Option::Some(r) maps to r. Vector index  *)
(* i maps to seat i in 0..NumSeats-1. Rust exclusive mutation is the       *)
(* action commit boundary. Read-only can_* methods and rejected admission   *)
(* attempts map to canonical stutter.                                      *)
(*                                                                         *)
(* 0..MaxResource is the deployment resource universe. For the Rust u64    *)
(* carrier, MaxResource is u64::MAX; TLC supplies a smaller model value.    *)
(***************************************************************************)
\* EXPECT: OK
EXTENDS Naturals, FiniteSets

CONSTANTS NumSeats, MaxResource, NullValue

ASSUME NumSeatsType == NumSeats \in Nat
ASSUME MaxResourceType == MaxResource \in Nat
ASSUME NullOutsideResources == NullValue \notin 0..MaxResource

Seats == IF NumSeats = 0 THEN {} ELSE 0..(NumSeats - 1)
ResourceDomain == 0..MaxResource

VARIABLES num_seats, allocation, effects, complete
vars == <<num_seats, allocation, effects, complete>>

TypeInvariant ==
    /\ num_seats = NumSeats
    /\ allocation \in [Seats -> ResourceDomain \cup {NullValue}]
    /\ effects \in [Seats -> ResourceDomain \cup {NullValue}]
    /\ complete \in BOOLEAN

ActuationScope == \A s \in Seats : effects[s] /= NullValue => allocation[s] /= NullValue
EffectFidelity == \A s \in Seats : effects[s] /= NullValue => effects[s] = allocation[s]
ReadyToFinish == \A s \in Seats : allocation[s] /= NullValue => effects[s] /= NullValue
PassCompleteness == complete => ReadyToFinish
ImplInvariant == TypeInvariant /\ EffectFidelity /\ PassCompleteness

\* ActuationPass::new(allocation, num_seats) postconditions.
Init ==
    /\ num_seats = NumSeats
    /\ allocation \in [Seats -> ResourceDomain \cup {NullValue}]
    /\ effects = [s \in Seats |-> NullValue]
    /\ complete = FALSE
    /\ ImplInvariant

\* allocate requires the unallocated, open seat and ensures one exact update.
ImplAllocate(s, r) ==
    /\ ImplInvariant
    /\ s \in Seats
    /\ r \in ResourceDomain
    /\ ~complete
    /\ allocation[s] = NullValue
    /\ allocation' = [allocation EXCEPT ![s] = r]
    /\ UNCHANGED <<num_seats, effects, complete>>
    /\ ImplInvariant'

\* deallocate carries the effects[s] = None ownership guard and exact frame.
ImplDeallocate(s) ==
    /\ ImplInvariant
    /\ s \in Seats
    /\ ~complete
    /\ allocation[s] /= NullValue
    /\ effects[s] = NullValue
    /\ allocation' = [allocation EXCEPT ![s] = NullValue]
    /\ UNCHANGED <<num_seats, effects, complete>>
    /\ ImplInvariant'

\* actuate copies the pre-state allocation value into the effect slot.
ImplActuate(s) ==
    /\ ImplInvariant
    /\ s \in Seats
    /\ ~complete
    /\ effects[s] = NullValue
    /\ allocation[s] /= NullValue
    /\ effects' = [effects EXCEPT ![s] = allocation[s]]
    /\ UNCHANGED <<num_seats, allocation, complete>>
    /\ ImplInvariant'

\* finish fuses ReadyToFinish with the closure write.
ImplFinish ==
    /\ ImplInvariant
    /\ ~complete
    /\ ReadyToFinish
    /\ complete' = TRUE
    /\ UNCHANGED <<num_seats, allocation, effects>>
    /\ ImplInvariant'

ImplReadOrReject == UNCHANGED vars

ImplNext ==
    \/ \E s \in Seats, r \in ResourceDomain : ImplAllocate(s, r)
    \/ \E s \in Seats : ImplDeallocate(s)
    \/ \E s \in Seats : ImplActuate(s)
    \/ ImplFinish
    \/ ImplReadOrReject

Spec == Init /\ [][ImplNext]_vars

A == INSTANCE ActuationPass WITH
        Seats <- Seats,
        Resources <- ResourceDomain,
        NULL <- NullValue,
        allocation <- allocation,
        effects <- effects,
        complete <- complete

Refinement == A!Spec
====
