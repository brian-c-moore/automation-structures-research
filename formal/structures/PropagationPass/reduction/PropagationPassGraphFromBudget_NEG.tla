---- MODULE PropagationPassGraphFromBudget_NEG ----
\* Refinement negative control. CUpdateNode reads live values instead of the
\* round-start snapshot, allowing a later update to consume an earlier update
\* from the same round. BudgetSafety and the iteration ledger remain intact;
\* the mapped step must violate SnapshotLocality.

EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Edges, MaxIterations, MaxValue

VARIABLES b_capacity, b_allocated, b_reserved, b_pending,
          values, snapshot, updated, changed, round

vars == <<b_capacity, b_allocated, b_reserved, b_pending,
          values, snapshot, updated, changed, round>>

Bgt == INSTANCE Budget WITH Capacity <- MaxIterations,
                            capacity <- b_capacity,
                            allocated <- b_allocated,
                            reserved <- b_reserved,
                            pending_eviction <- b_pending

BudgetSafety == Bgt!SafetyInvariant

InNbr(n) == {m \in Nodes : <<m, n>> \in Edges}
EdgesPath == {<<1, 2>>, <<2, 3>>}
Combine(n, vals) ==
    IF \E m \in InNbr(n) : vals[m] < vals[n] THEN vals[n] - 1 ELSE vals[n]

IterationView == b_allocated - (IF round = "running" THEN 1 ELSE 0)

TypeInvariant ==
    /\ b_capacity = MaxIterations
    /\ b_allocated \in 0..MaxIterations
    /\ b_reserved = 0
    /\ b_pending = 0
    /\ values   \in [Nodes -> 0..MaxValue]
    /\ snapshot \in [Nodes -> 0..MaxValue]
    /\ updated  \subseteq Nodes
    /\ changed  \in BOOLEAN
    /\ round    \in {"idle", "running"}

Init ==
    /\ b_capacity = MaxIterations
    /\ b_allocated = 0
    /\ b_reserved = 0
    /\ b_pending = 0
    /\ values \in [Nodes -> 0..MaxValue]
    /\ snapshot = values
    /\ updated = {}
    /\ changed = TRUE
    /\ round = "idle"

CStartRound ==
    /\ round = "idle"
    /\ changed = TRUE
    /\ b_allocated + b_reserved + b_pending + 1 <= b_capacity
    /\ b_allocated' = b_allocated + 1
    /\ snapshot' = values
    /\ updated' = {}
    /\ round' = "running"
    /\ UNCHANGED <<b_capacity, b_reserved, b_pending, values, changed>>

\* Fault: read live values instead of the round-start snapshot.
CUpdateNode(n) ==
    /\ round = "running"
    /\ n \notin updated
    /\ values' = [values EXCEPT ![n] = Combine(n, values)]
    /\ updated' = updated \cup {n}
    /\ UNCHANGED <<b_capacity, b_allocated, b_reserved, b_pending,
                   snapshot, changed, round>>

CEndRound ==
    /\ round = "running"
    /\ updated = Nodes
    /\ changed' = (values /= snapshot)
    /\ round' = "idle"
    /\ UNCHANGED <<b_capacity, b_allocated, b_reserved, b_pending,
                   values, snapshot, updated>>

CTerminate ==
    /\ round = "idle"
    /\ (changed = FALSE \/ b_allocated = MaxIterations)
    /\ UNCHANGED vars

Next ==
    \/ CStartRound
    \/ \E n \in Nodes : CUpdateNode(n)
    \/ CEndRound
    \/ CTerminate

Fairness ==
    /\ WF_vars(CStartRound)
    /\ \A n \in Nodes : WF_vars(CUpdateNode(n))
    /\ WF_vars(CEndRound)

Spec == Init /\ [][Next]_vars /\ Fairness

PPG == INSTANCE PropagationPassGraph WITH
        values        <- values,
        snapshot      <- snapshot,
        updated       <- updated,
        iteration     <- IterationView,
        changed       <- changed,
        round         <- round,
        Nodes         <- Nodes,
        Edges         <- Edges,
        MaxIterations <- MaxIterations,
        MaxValue      <- MaxValue

PropagationPassGraphRefinement == PPG!Spec
====
