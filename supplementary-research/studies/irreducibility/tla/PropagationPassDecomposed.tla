---------------------- MODULE PropagationPassDecomposed ----------------------
(* Splits PropagationPass's Propagate: CheckPropagate holds its guard
   (`changed = TRUE` and `iteration < MaxIterations`); PerformPropagate applies
   its writes. Two propagators pass the guard at iteration = MaxIterations - 1
   and both perform, so iteration exceeds the bound, violating BoundedIteration.
   Adds `pc` and a second propagator. *)
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, MaxIterations, MaxValue

VARIABLES values, iteration, changed, pc

vars == <<values, iteration, changed, pc>>

Procs == {"p1", "p2"}

TypeInvariant ==
    /\ values \in [Nodes -> 0..MaxValue]
    /\ iteration \in Nat
    /\ changed \in BOOLEAN

BoundedIteration ==
    iteration <= MaxIterations

Init ==
    /\ values \in [Nodes -> 0..MaxValue]
    /\ iteration = 0
    /\ changed = TRUE
    /\ pc = [p \in Procs |-> "idle"]

(* Step 1: canonical Propagate's guard, and no mutation *)
CheckPropagate(p) ==
    /\ pc[p] = "idle"
    /\ changed = TRUE
    /\ iteration < MaxIterations
    /\ pc' = [pc EXCEPT ![p] = "checked"]
    /\ UNCHANGED <<values, iteration, changed>>

(* Step 2: canonical Propagate's mutation, on a guard already passed *)
PerformPropagate(p) ==
    /\ pc[p] = "checked"
    /\ \E new_values \in [Nodes -> 0..MaxValue] :
        /\ changed' = (new_values /= values)
        /\ values' = new_values
        /\ iteration' = iteration + 1
    /\ pc' = [pc EXCEPT ![p] = "idle"]

Terminate ==
    /\ (changed = FALSE \/ iteration = MaxIterations)
    /\ UNCHANGED vars

Next ==
    \/ \E p \in Procs : CheckPropagate(p) \/ PerformPropagate(p)
    \/ Terminate

Spec == Init /\ [][Next]_vars
=============================================================================
