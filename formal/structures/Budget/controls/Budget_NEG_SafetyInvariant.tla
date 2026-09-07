---- MODULE Budget_NEG_SafetyInvariant ----
\* Negative control for Budget.SafetyInvariant. TryAllocate omits the ledger
\* ceiling test and always increments allocated. With only SafetyInvariant
\* declared, a positive amount at full capacity must violate the bound.
\* All other actions retain the carrier transition relation.

EXTENDS Naturals

CONSTANT Capacity

VARIABLES capacity, allocated, reserved, pending_eviction

vars == <<capacity, allocated, reserved, pending_eviction>>

TypeInvariant ==
    /\ capacity \in Nat
    /\ allocated \in Nat
    /\ reserved \in Nat
    /\ pending_eviction \in Nat

SafetyInvariant ==
    allocated + reserved + pending_eviction <= capacity

Init ==
    /\ capacity = Capacity
    /\ allocated = 0
    /\ reserved = 0
    /\ pending_eviction = 0

\* ---- MUTATION BEGINS -- to the closing marker, this replaces the base text.
TryAllocate(amount) ==
    /\ allocated' = allocated + amount
    /\ UNCHANGED <<capacity, reserved, pending_eviction>>
\* ---- MUTATION ENDS.

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

====
