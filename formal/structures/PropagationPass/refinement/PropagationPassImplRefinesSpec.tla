---- MODULE PropagationPassImplRefinesSpec ----
(***************************************************************************)
(* Contract transcription for PropagationPass. Source:                    *)
(* crate://automation-structures/0.2.3/src/primitives/propagation_pass.rs.         *)
(*                                                                         *)
(* num_nodes, max_iterations, max_value, and edges are immutable fields.    *)
(* The edge Vec maps to EdgeSet; its order is hidden. values and snapshot   *)
(* map indexwise. The updated bool Vec maps to its set of true indices.      *)
(* Round::Idle and Round::Running map to the two canonical strings.          *)
(*                                                                         *)
(* Verus proves finite action contracts, not scheduler fairness.            *)
(* SchedulerFairnessRely is therefore explicit and is the only temporal     *)
(* premise used to refine the canonical liveness-bearing Spec.              *)
(***************************************************************************)
\* EXPECT: OK
EXTENDS Naturals, FiniteSets

CONSTANTS NumNodes, EdgeSet, MaxIterations, MaxValue
ASSUME NumNodesType == NumNodes \in Nat
ASSUME MaxIterationsType == MaxIterations \in Nat
ASSUME MaxValueType == MaxValue \in Nat

Nodes == IF NumNodes = 0 THEN {} ELSE 0..(NumNodes - 1)
ASSUME EdgeSetType == EdgeSet \subseteq (Nodes \X Nodes)

InNbr(n) == {m \in Nodes : <<m, n>> \in EdgeSet}
Combine(n, vals) ==
    IF \E m \in InNbr(n) : vals[m] < vals[n] THEN vals[n] - 1 ELSE vals[n]

ConfiguredEdges == {<<0, 1>>, <<1, 2>>}

VARIABLES num_nodes, max_iterations, max_value, edges,
          values, snapshot, updated, iteration, changed, round

vars == <<num_nodes, max_iterations, max_value, edges,
          values, snapshot, updated, iteration, changed, round>>

TypeInvariant ==
    /\ num_nodes = NumNodes
    /\ max_iterations = MaxIterations
    /\ max_value = MaxValue
    /\ edges = EdgeSet
    /\ values \in [Nodes -> 0..MaxValue]
    /\ snapshot \in [Nodes -> 0..MaxValue]
    /\ updated \subseteq Nodes
    /\ iteration \in Nat
    /\ changed \in BOOLEAN
    /\ round \in {"idle", "running"}
IterationBound == iteration <= max_iterations
SnapshotLocality == \A n \in updated : values[n] = Combine(n, snapshot)
RoundBound == round = "running" => iteration < max_iterations
RunningChanged == round = "running" => changed
AllUpdated == updated = Nodes
SettledOk == ~changed => values = snapshot /\ AllUpdated
ImplInvariant ==
    TypeInvariant /\ IterationBound /\ SnapshotLocality /\ RoundBound
        /\ RunningChanged /\ SettledOk

Init ==
    /\ num_nodes = NumNodes
    /\ max_iterations = MaxIterations
    /\ max_value = MaxValue
    /\ edges = EdgeSet
    /\ values \in [Nodes -> 0..MaxValue]
    /\ snapshot = values
    /\ updated = {}
    /\ iteration = 0
    /\ changed = TRUE
    /\ round = "idle"
    /\ ImplInvariant

ImplStartRound ==
    /\ ImplInvariant
    /\ round = "idle"
    /\ changed
    /\ iteration < max_iterations
    /\ snapshot' = values
    /\ updated' = {}
    /\ round' = "running"
    /\ UNCHANGED <<num_nodes, max_iterations, max_value, edges,
                    values, iteration, changed>>
    /\ ImplInvariant'

ImplUpdateNode(n) ==
    /\ ImplInvariant
    /\ round = "running"
    /\ n \in Nodes
    /\ n \notin updated
    /\ values' = [values EXCEPT ![n] = Combine(n, snapshot)]
    /\ updated' = updated \cup {n}
    /\ UNCHANGED <<num_nodes, max_iterations, max_value, edges,
                    snapshot, iteration, changed, round>>
    /\ ImplInvariant'

ImplEndRound ==
    /\ ImplInvariant
    /\ round = "running"
    /\ AllUpdated
    /\ changed' = (values /= snapshot)
    /\ iteration' = iteration + 1
    /\ round' = "idle"
    /\ UNCHANGED <<num_nodes, max_iterations, max_value, edges,
                    values, snapshot, updated>>
    /\ ImplInvariant'

ImplTerminateOrRead == UNCHANGED vars

ImplNext ==
    \/ ImplStartRound
    \/ \E n \in Nodes : ImplUpdateNode(n)
    \/ ImplEndRound
    \/ ImplTerminateOrRead

P == INSTANCE PropagationPassGraph WITH
        Nodes <- Nodes,
        Edges <- EdgeSet,
        MaxIterations <- MaxIterations,
        MaxValue <- MaxValue,
        values <- values,
        snapshot <- snapshot,
        updated <- updated,
        iteration <- iteration,
        changed <- changed,
        round <- round

SchedulerFairnessRely == P!Fairness
Spec == Init /\ [][ImplNext]_vars /\ SchedulerFairnessRely
SafetyRefinement == P!Init /\ [][P!Next]_(P!vars)
Refinement == P!Spec
====
