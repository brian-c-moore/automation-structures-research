---- MODULE BudgetImplRefinesSpec_NEG ----
(*****************************************************************************)
(* Refinement control for BudgetImplRefinesSpec. ImplCommitReservation moves *)
(* amount from allocated to reserved, reversing the canonical transfer.      *)
(* The additional amount <= allocated guard keeps all fields natural, and    *)
(* the transfer preserves Used, so TypeInvariant and SafetyInvariant remain  *)
(* true. No canonical Budget action implements this direction of transfer;   *)
(* Refinement must therefore fail independently of the carrier invariants.    *)
(*****************************************************************************)
\* EXPECT: VIOLATION
EXTENDS Naturals

CONSTANTS Capacity, MaxAmount

ASSUME CapacityType  == Capacity  \in Nat
ASSUME MaxAmountType == MaxAmount \in Nat

Amounts == 0..MaxAmount

VARIABLES capacity, allocated, reserved, pending_eviction

vars == <<capacity, allocated, reserved, pending_eviction>>

Used == allocated + reserved + pending_eviction

SafetyInvariant == Used <= capacity

TypeInvariant ==
    /\ capacity \in Nat
    /\ allocated \in Nat
    /\ reserved \in Nat
    /\ pending_eviction \in Nat

Init ==
    /\ capacity = Capacity
    /\ allocated = 0
    /\ reserved = 0
    /\ pending_eviction = 0

ImplTryAllocate(amount) ==
    /\ SafetyInvariant
    /\ IF Used + amount <= capacity
       THEN allocated' = allocated + amount
       ELSE allocated' = allocated
    /\ UNCHANGED <<capacity, reserved, pending_eviction>>

ImplReserve(amount) ==
    /\ SafetyInvariant
    /\ IF Used + amount <= capacity
       THEN reserved' = reserved + amount
       ELSE reserved' = reserved
    /\ UNCHANGED <<capacity, allocated, pending_eviction>>

\* Fault. Positive module:
\*     allocated' = allocated + amount /\ reserved' = reserved - amount
ImplCommitReservation(amount) ==
    /\ SafetyInvariant
    /\ amount <= reserved
    /\ amount <= allocated        \* keeps the mutant well-typed (see header)
    /\ allocated' = allocated - amount
    /\ reserved' = reserved + amount
    /\ UNCHANGED <<capacity, pending_eviction>>

ImplRelease(amount) ==
    /\ SafetyInvariant
    /\ amount <= allocated
    /\ allocated' = allocated - amount
    /\ UNCHANGED <<capacity, reserved, pending_eviction>>

ImplMarkEviction(amount) ==
    /\ SafetyInvariant
    /\ amount <= allocated
    /\ allocated' = allocated - amount
    /\ pending_eviction' = pending_eviction + amount
    /\ UNCHANGED <<capacity, reserved>>

ImplCompleteEviction(amount) ==
    /\ SafetyInvariant
    /\ amount <= pending_eviction
    /\ pending_eviction' = pending_eviction - amount
    /\ UNCHANGED <<capacity, allocated, reserved>>

Next ==
    \/ \E a \in Amounts : ImplTryAllocate(a)
    \/ \E a \in Amounts : ImplReserve(a)
    \/ \E a \in Amounts : ImplCommitReservation(a)
    \/ \E a \in Amounts : ImplRelease(a)
    \/ \E a \in Amounts : ImplMarkEviction(a)
    \/ \E a \in Amounts : ImplCompleteEviction(a)

Spec == Init /\ [][Next]_vars

B == INSTANCE Budget WITH
        Capacity         <- Capacity,
        capacity         <- capacity,
        allocated        <- allocated,
        reserved         <- reserved,
        pending_eviction <- pending_eviction

Refinement == B!Spec
====
