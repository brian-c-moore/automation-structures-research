---- MODULE Budget ----
EXTENDS Naturals

CONSTANT Capacity

VARIABLES capacity, allocated, reserved, pending_eviction

vars == <<capacity, allocated, reserved, pending_eviction>>

TypeInvariant ==
    /\ capacity \in Nat
    /\ allocated \in Nat
    /\ reserved \in Nat
    /\ pending_eviction \in Nat

\* Capacity contract. TryAllocate and Reserve test the complete ledger before
\* adding to it. CommitReservation and MarkEviction transfer quantity between
\* terms; Release and CompleteEviction remove quantity. The allocation check
\* and update are one atomic action here. An implementation that separates
\* them must re-establish the same bound at its commit point.
SafetyInvariant ==
    allocated + reserved + pending_eviction <= capacity

Init ==
    /\ capacity = Capacity
    /\ allocated = 0
    /\ reserved = 0
    /\ pending_eviction = 0

TryAllocate(amount) ==
    IF allocated + reserved + pending_eviction + amount <= capacity
    THEN /\ allocated' = allocated + amount
         /\ UNCHANGED <<capacity, reserved, pending_eviction>>
    ELSE UNCHANGED vars

Reserve(amount) ==
    IF allocated + reserved + pending_eviction + amount <= capacity
    THEN /\ reserved' = reserved + amount
         /\ UNCHANGED <<capacity, allocated, pending_eviction>>
    ELSE UNCHANGED vars

CommitReservation(amount) ==
    /\ amount <= reserved
    /\ allocated' = allocated + amount
    /\ reserved' = reserved - amount
    /\ UNCHANGED <<capacity, pending_eviction>>

Release(amount) ==
    /\ amount <= allocated
    /\ allocated' = allocated - amount
    /\ UNCHANGED <<capacity, reserved, pending_eviction>>

MarkEviction(amount) ==
    /\ amount <= allocated
    /\ allocated' = allocated - amount
    /\ pending_eviction' = pending_eviction + amount
    /\ UNCHANGED <<capacity, reserved>>

CompleteEviction(amount) ==
    /\ amount <= pending_eviction
    /\ pending_eviction' = pending_eviction - amount
    /\ UNCHANGED <<capacity, allocated, reserved>>

Next ==
    \/ \E a \in 1..capacity : TryAllocate(a)
    \/ \E a \in 1..capacity : Reserve(a)
    \/ \E a \in 1..reserved : CommitReservation(a)
    \/ \E a \in 1..allocated : Release(a)
    \/ \E a \in 1..allocated : MarkEviction(a)
    \/ \E a \in 1..pending_eviction : CompleteEviction(a)

Spec == Init /\ [][Next]_vars

\* Spec => []SafetyInvariant: proved as SafetyInvariantSafety in Budget_Proof.
====
