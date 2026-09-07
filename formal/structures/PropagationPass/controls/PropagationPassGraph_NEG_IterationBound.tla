---- MODULE PropagationPassGraph_NEG_IterationBound ----
\* Negative control for IterationBound. StartRound omits the admission check
\* iteration < MaxIterations, allowing a further round to close past the limit.

EXTENDS Naturals, FiniteSets

CONSTANTS Nodes,
          Edges,
          MaxIterations,
          MaxValue

VARIABLES values,
          snapshot,
          updated,
          iteration,
          changed,
          round

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

IterationBound ==
    iteration <= MaxIterations

SnapshotLocality ==
    \A n \in updated : values[n] = Combine(n, snapshot)

Init ==
    /\ values \in [Nodes -> 0..MaxValue]
    /\ snapshot = values
    /\ updated = {}
    /\ iteration = 0
    /\ changed = TRUE
    /\ round = "idle"

\* ---- MUTATION BEGINS -- to the closing marker, this replaces the base text.
StartRound ==
    /\ round = "idle"
    /\ changed = TRUE
\* ---- MUTATION ENDS.
    /\ snapshot' = values
    /\ updated' = {}
    /\ round' = "running"
    /\ UNCHANGED <<values, iteration, changed>>

UpdateNode(n) ==
    /\ round = "running"
    /\ n \notin updated
    /\ values' = [values EXCEPT ![n] = Combine(n, snapshot)]
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

Fairness ==
    /\ WF_vars(StartRound)
    /\ \A n \in Nodes : WF_vars(UpdateNode(n))
    /\ WF_vars(EndRound)

Spec == Init /\ [][Next]_vars /\ Fairness

EventualSettledOrIterationLimit ==
    <>(changed = FALSE \/ iteration = MaxIterations)

LocallyConsistent ==
    \A n \in Nodes : values[n] = Combine(n, values)

====
