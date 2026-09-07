---- MODULE PropagationPassImplRefinesSpec_NEG ----
(***************************************************************************)
(* Isolated snapshot fault: one node reads current values instead of the    *)
(* frozen round snapshot. Typing, iteration, phase, and settled-state        *)
(* predicates remain checked. SnapshotLocality and action refinement fail.  *)
(***************************************************************************)
\* EXPECT: VIOLATION
EXTENDS PropagationPassImplRefinesSpec

AdjacentInvariant ==
    TypeInvariant /\ IterationBound /\ RoundBound /\ RunningChanged /\ SettledOk

FaultUpdateNode(n) ==
    /\ AdjacentInvariant
    /\ round = "running"
    /\ n \in Nodes
    /\ n \notin updated
    /\ Combine(n, values) /= Combine(n, snapshot)
    /\ values' = [values EXCEPT ![n] = Combine(n, values)]
    /\ updated' = updated \cup {n}
    /\ UNCHANGED <<num_nodes, max_iterations, max_value, edges,
                    snapshot, iteration, changed, round>>
    /\ AdjacentInvariant'

FaultNext ==
    \/ ImplStartRound
    \/ \E n \in Nodes : ImplUpdateNode(n)
    \/ \E n \in Nodes : FaultUpdateNode(n)
    \/ ImplEndRound
    \/ ImplTerminateOrRead

FaultRefinement == SafetyRefinement
====
