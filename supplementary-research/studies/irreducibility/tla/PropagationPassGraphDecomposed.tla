----------------------- MODULE PropagationPassGraphDecomposed -----------------------
(* Irreducibility-by-construction for the concept-faithful
   PropagationPassGraph.

   This module is PropagationPassGraph with ONE change to the TRANSITION
   RELATION: UpdateNode's combine reads the LIVE `values` instead of the
   round-start `snapshot`. Everything else in the machine -- the topology,
   the bound, the round structure, the constants and the invariants -- is
   the base module's.

   The second difference this module carries: the base's `Fairness` conjunct
   is dropped from `Spec`, and with it the base's `Convergence` liveness
   property from this module and its .cfg.
   The drop is inert for what this instrument checks -- WF conjuncts
   constrain no reachable state, so it can neither manufacture the
   LocalUpdate violation nor mask a BoundedIteration one -- and liveness is
   not this instrument's question.

   That single change is the Jacobi-to-Gauss-Seidel decomposition: it
   separates "take the round's snapshot" from "read the values this round's
   messages carry", which the base module commits as one thing. It is the
   decomposition the composition catalog's own Bellman-Ford row rules out
   when it requires "per-round snapshot isolation".

   TLC must find a violation of LocalUpdate: once a node's in-neighbour has
   already been updated in the current round, that node reads a same-round
   write, and its value is no longer the local combine of the round-start
   snapshot. The fixed point reached then depends on the order nodes are
   visited in -- which is exactly the governance the primitive supplies and
   the decomposition destroys.

   BoundedIteration still holds here: the bound is a separate obligation and
   this decomposition does not touch it. The two obligations fail
   independently, which is why they are stated separately.                   *)
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Edges, MaxIterations, MaxValue

VARIABLES values, snapshot, updated, iteration, changed, round

vars == <<values, snapshot, updated, iteration, changed, round>>

InNbr(n) == {m \in Nodes : <<m, n>> \in Edges}

EdgesPath == {<<1, 2>>, <<2, 3>>}

Combine(n, vals) ==
    IF \E m \in InNbr(n) : vals[m] < vals[n] THEN vals[n] - 1 ELSE vals[n]

TypeInvariant ==
    /\ values   \in [Nodes -> 0..MaxValue]
    /\ snapshot \in [Nodes -> 0..MaxValue]
    /\ updated  \subseteq Nodes
    /\ iteration \in Nat
    /\ changed  \in BOOLEAN
    /\ round    \in {"idle", "running"}

BoundedIteration ==
    iteration <= MaxIterations

LocalUpdate ==
    \A n \in updated : values[n] = Combine(n, snapshot)

Init ==
    /\ values \in [Nodes -> 0..MaxValue]
    /\ snapshot = values
    /\ updated = {}
    /\ iteration = 0
    /\ changed = TRUE
    /\ round = "idle"

StartRound ==
    /\ round = "idle"
    /\ changed = TRUE
    /\ iteration < MaxIterations
    /\ snapshot' = values
    /\ updated' = {}
    /\ round' = "running"
    /\ UNCHANGED <<values, iteration, changed>>

(* THE DECOMPOSITION: the combine reads the LIVE `values`, not the
   round-start `snapshot`. One substitution; nothing else differs. *)
UpdateNode(n) ==
    /\ round = "running"
    /\ n \notin updated
    /\ values' = [values EXCEPT ![n] = Combine(n, values)]
    /\ updated' = updated \cup {n}
    /\ UNCHANGED <<snapshot, iteration, changed, round>>

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

Spec == Init /\ [][Next]_vars

\* TLC finds a violation of LocalUpdate.
=============================================================================
