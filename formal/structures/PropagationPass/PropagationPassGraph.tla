---- MODULE PropagationPassGraph ----
(* Graph propagation in explicit snapshot-isolated rounds.

   StartRound freezes values. UpdateNode computes one target from its own and
   its in-neighbours' snapshot values. EndRound closes only after every node
   has been updated and charges one iteration.

   Obligations:
     IterationBound -- iteration never exceeds MaxIterations.
     SnapshotLocality -- every updated node holds the declared local combine
                         of the common round-start snapshot.
     EventualSettledOrIterationLimit -- under finite Nodes and the stated weak
                                        fairness, the behavior eventually
                                        settles or reaches the iteration limit.

   ConsistencyAtFixedPoint is a corollary of SnapshotLocality when changed is false,
   not an independent checked invariant. Runtime scheduler fairness is an
   environment rely. The finite instance fixes one relaxation rule; the
   structural guarantee is locality and snapshot isolation, not a universal
   convergence theorem for arbitrary domain combines.                        *)
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes,          \* the graph's vertices
          Edges,          \* the graph's directed edges: messages flow m -> n
          MaxIterations,  \* maximum number of completed rounds
          MaxValue

VARIABLES values,     \* the per-node value being propagated
          snapshot,   \* the round-start values every node in the round reads
          updated,    \* the nodes already updated in the current round
          iteration,
          changed,
          round       \* "idle" between rounds, "running" inside one

vars == <<values, snapshot, updated, iteration, changed, round>>

\* Messages flow from source to target, so a node reads its in-neighbours.
\* Edges is constant; the proof is parametric over the topology.
InNbr(n) == {m \in Nodes : <<m, n>> \in Edges}

\* Finite TLC topology, supplied through a configuration definition override.
EdgesPath == {<<1, 2>>, <<2, 3>>}

\* The domain-supplied local combine: a node relaxes by one step when some
\* in-neighbour is strictly better. Local by construction -- it reads only
\* vals[n] and vals[m] for m in InNbr(n).
Combine(n, vals) ==
    IF \E m \in InNbr(n) : vals[m] < vals[n] THEN vals[n] - 1 ELSE vals[n]

TypeInvariant ==
    /\ values   \in [Nodes -> 0..MaxValue]
    /\ snapshot \in [Nodes -> 0..MaxValue]
    /\ updated  \subseteq Nodes
    /\ iteration \in Nat
    /\ changed  \in BOOLEAN
    /\ round    \in {"idle", "running"}

\* Completed rounds never exceed the declared limit.
IterationBound ==
    iteration <= MaxIterations

\* Every updated node is computed from the common round-start snapshot and
\* only through Combine's own node/in-neighbour reads.
SnapshotLocality ==
    \A n \in updated : values[n] = Combine(n, snapshot)

Init ==
    /\ values \in [Nodes -> 0..MaxValue]
    /\ snapshot = values
    /\ updated = {}
    /\ iteration = 0
    /\ changed = TRUE
    /\ round = "idle"

\* Take the snapshot this round's messages are read from.
StartRound ==
    /\ round = "idle"
    /\ changed = TRUE
    /\ iteration < MaxIterations
    /\ snapshot' = values
    /\ updated' = {}
    /\ round' = "running"
    /\ UNCHANGED <<values, iteration, changed>>

\* Compute and commit one node from the immutable round snapshot.
UpdateNode(n) ==
    /\ round = "running"
    /\ n \notin updated
    /\ values' = [values EXCEPT ![n] = Combine(n, snapshot)]
    /\ updated' = updated \cup {n}
    /\ UNCHANGED <<snapshot, iteration, changed, round>>

\* Close the round: detect whether anything moved, and charge the iteration.
EndRound ==
    /\ round = "running"
    /\ updated = Nodes
    /\ changed' = (values /= snapshot)
    /\ iteration' = iteration + 1
    /\ round' = "idle"
    /\ UNCHANGED <<values, snapshot, updated>>

Terminate ==
    /\ round = "idle"
    /\ (changed = FALSE \/ iteration = MaxIterations)
    /\ UNCHANGED vars

Next ==
    \/ StartRound
    \/ \E n \in Nodes : UpdateNode(n)
    \/ EndRound
    \/ Terminate

\* Weak fairness is stated separately for round admission, each node update,
\* and round closure.
Fairness ==
    /\ WF_vars(StartRound)
    /\ \A n \in Nodes : WF_vars(UpdateNode(n))
    /\ WF_vars(EndRound)

Spec == Init /\ [][Next]_vars /\ Fairness

\* Under finite Nodes and the fairness above, the pass always settles or
\* reaches its iteration ceiling.
EventualSettledOrIterationLimit ==
    <>(changed = FALSE \/ iteration = MaxIterations)

\* Derived fixed-point predicate. SnapshotLocality and changed = FALSE imply
\* this predicate; it is proved as a corollary rather than checked separately.
LocallyConsistent ==
    \A n \in Nodes : values[n] = Combine(n, values)

\* Spec => []TypeInvariant, []IterationBound, []SnapshotLocality: proved in
\* PropagationPassGraph_Proof.tla, along with the LocallyConsistent
\* corollary.
====
