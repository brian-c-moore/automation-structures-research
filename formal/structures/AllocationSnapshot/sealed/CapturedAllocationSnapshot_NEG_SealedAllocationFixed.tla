---- MODULE CapturedAllocationSnapshot_NEG_SealedAllocationFixed ----
\* Declaration-preserving control: admit the existing Next after sealing.
EXTENDS AllocationSnapshotFromRegistry

VARIABLES sealed, captured_entries, captured_budget

capture_vars == <<vars, sealed, captured_entries, captured_budget>>
BudgetObservation == <<capacity, allocated, reserved, pending_eviction>>

CaptureInit ==
    /\ Init
    /\ sealed = FALSE
    /\ captured_entries = {}
    /\ captured_budget = <<BudgetCapacity, 0, 0, 0>>

CaptureAccept ==
    \* MUTATION: omit only the ~sealed admission guard.
    /\ Next
    /\ UNCHANGED <<sealed, captured_entries, captured_budget>>

Seal ==
    /\ ~sealed
    /\ sealed' = TRUE
    /\ captured_entries' = entries
    /\ captured_budget' = BudgetObservation
    /\ UNCHANGED vars

CaptureNext == CaptureAccept \/ Seal
CaptureSpec == CaptureInit /\ [][CaptureNext]_capture_vars

SealedAllocationFixed ==
    sealed => entries = captured_entries /\ BudgetObservation = captured_budget
====
