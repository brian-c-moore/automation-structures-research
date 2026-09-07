---- MODULE BudgetFromGlue ----
\* Pure-glue re-encoding of Budget. Four counters hold the complete Budget
\* state, and the actions reproduce its ledger transitions under a variable
\* relabeling. The construction therefore proves definitional reducibility to
\* glue; it does not identify a retained component that owns the capacity
\* bound or the combined admission/reservation protocol.
EXTENDS Naturals

CONSTANT Capacity

\* Four CF-005 Counters. No component state.
VARIABLES c_capacity, c_allocated, c_reserved, c_pending

vars == <<c_capacity, c_allocated, c_reserved, c_pending>>

TypeInvariant ==
    /\ c_capacity \in Nat
    /\ c_allocated \in Nat
    /\ c_reserved \in Nat
    /\ c_pending \in Nat

\* Budget's capacity bound restated over the glue counters.
MappedSafety ==
    c_allocated + c_reserved + c_pending <= c_capacity

Init ==
    /\ c_capacity = Capacity
    /\ c_allocated = 0
    /\ c_reserved = 0
    /\ c_pending = 0

\* Budget's own actions, carried verbatim over the counters.
TryAllocate(amount) ==
    IF c_allocated + c_reserved + c_pending + amount <= c_capacity
    THEN /\ c_allocated' = c_allocated + amount
         /\ UNCHANGED <<c_capacity, c_reserved, c_pending>>
    ELSE UNCHANGED vars

Reserve(amount) ==
    IF c_allocated + c_reserved + c_pending + amount <= c_capacity
    THEN /\ c_reserved' = c_reserved + amount
         /\ UNCHANGED <<c_capacity, c_allocated, c_pending>>
    ELSE UNCHANGED vars

CommitReservation(amount) ==
    /\ amount <= c_reserved
    /\ c_allocated' = c_allocated + amount
    /\ c_reserved' = c_reserved - amount
    /\ UNCHANGED <<c_capacity, c_pending>>

Release(amount) ==
    /\ amount <= c_allocated
    /\ c_allocated' = c_allocated - amount
    /\ UNCHANGED <<c_capacity, c_reserved, c_pending>>

MarkEviction(amount) ==
    /\ amount <= c_allocated
    /\ c_allocated' = c_allocated - amount
    /\ c_pending' = c_pending + amount
    /\ UNCHANGED <<c_capacity, c_reserved>>

CompleteEviction(amount) ==
    /\ amount <= c_pending
    /\ c_pending' = c_pending - amount
    /\ UNCHANGED <<c_capacity, c_allocated, c_reserved>>

Next ==
    \/ \E a \in 1..c_capacity : TryAllocate(a)
    \/ \E a \in 1..c_capacity : Reserve(a)
    \/ \E a \in 1..c_reserved : CommitReservation(a)
    \/ \E a \in 1..c_allocated : Release(a)
    \/ \E a \in 1..c_allocated : MarkEviction(a)
    \/ \E a \in 1..c_pending : CompleteEviction(a)

Spec == Init /\ [][Next]_vars

\* --- Refinement mapping to Budget ---
BGT == INSTANCE Budget WITH
        capacity         <- c_capacity,
        allocated        <- c_allocated,
        reserved         <- c_reserved,
        pending_eviction <- c_pending,
        Capacity         <- Capacity

BudgetRefinement == BGT!Spec
====
