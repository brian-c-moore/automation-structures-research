---- MODULE CapturedAllocationSnapshot ----
\* Sealed profile of the existing Registry + Budget construction.
\* Captured observations are ghost witnesses, not additional runtime owners.
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
    /\ ~sealed
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

\* BudgetSafety, RegistryUnique and ASRefinement retain their original meanings.
====
