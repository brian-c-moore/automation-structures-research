--------------------------- MODULE BudgetDecomposed ---------------------------
(* Negative decomposition witness for Budget check-act stability. CheckFit
   reads the unit-allocation guard, ConcurrentAllocate may consume the
   remaining capacity, and PerformAllocation commits from the stale check.
   The resulting trace violates SafetyInvariant.

   The model covers only unit TryAllocate behavior. It omits reservation,
   release, and eviction state and actions, so it is not a refinement of the
   complete Budget carrier and makes no claim about its four-term ledger
   inequality.                                                               *)
EXTENDS Naturals, FiniteSets

CONSTANT Capacity   \* e.g. 4
CONSTANT NULL

VARIABLE allocated, checked, pc

vars == <<allocated, checked, pc>>

\* Two processes supply the checked operation and the interfering allocation.
Procs == {"p1", "p2"}

Init ==
    /\ allocated = 0
    /\ checked = [p \in Procs |-> FALSE]
    /\ pc = [p \in Procs |-> "idle"]

(* Record a successful guard evaluation without allocating. *)
CheckFit(p) ==
    /\ pc[p] = "idle"
    /\ allocated < Capacity
    /\ checked' = [checked EXCEPT ![p] = TRUE]
    /\ pc' = [pc EXCEPT ![p] = "checked"]
    /\ UNCHANGED allocated

(* Commit using the recorded guard result without rechecking capacity. *)
PerformAllocation(p) ==
    /\ pc[p] = "checked"
    /\ checked[p] = TRUE
    /\ allocated' = allocated + 1
    /\ checked' = [checked EXCEPT ![p] = FALSE]
    /\ pc' = [pc EXCEPT ![p] = "idle"]

(* Consume capacity while another process is between CheckFit and commit. *)
ConcurrentAllocate(p) ==
    /\ pc[p] = "idle"
    /\ allocated < Capacity
    /\ allocated' = allocated + 1
    /\ UNCHANGED <<checked, pc>>

Next ==
    \E p \in Procs :
        \/ CheckFit(p)
        \/ PerformAllocation(p)
        \/ ConcurrentAllocate(p)

SafetyInvariant == allocated <= Capacity

Spec == Init /\ [][Next]_vars
=============================================================================
