---- MODULE PropagationPassGraphFromBudget ----
\* Budget-backed construction of PropagationPassGraph. CStartRound charges one
\* Budget unit; IterationView discounts that in-flight charge until CEndRound.
\*
\* Budget supplies the iteration ceiling only. values, snapshot, updated,
\* changed, and round are additional state, and SnapshotLocality is established
\* by the construction rather than by Budget. The refinement therefore does
\* not attribute propagation locality to Budget itself.
\*
\* Each construction action is an atomic commit. The proof establishes the
\* mapped behavior under that commit boundary.

EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Edges, MaxIterations, MaxValue

\* Budget component state (b_*) + the five glue variables.
VARIABLES b_capacity, b_allocated, b_reserved, b_pending,
          values, snapshot, updated, changed, round

vars == <<b_capacity, b_allocated, b_reserved, b_pending,
          values, snapshot, updated, changed, round>>

Bgt == INSTANCE Budget WITH Capacity <- MaxIterations,
                            capacity <- b_capacity,
                            allocated <- b_allocated,
                            reserved <- b_reserved,
                            pending_eviction <- b_pending

\* Safety predicate of the Budget component.
BudgetSafety == Bgt!SafetyInvariant

\* The target's topology and domain-supplied combine, written verbatim.
InNbr(n) == {m \in Nodes : <<m, n>> \in Edges}
EdgesPath == {<<1, 2>>, <<2, 3>>}
Combine(n, vals) ==
    IF \E m \in InNbr(n) : vals[m] < vals[n] THEN vals[n] - 1 ELSE vals[n]

\* Completed-round count derived from the allocation ledger.
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

\* Target snapshot-locality obligation over the construction state. It is not
\* implied by BudgetSafety.
MappedSnapshotLocality ==
    \A n \in updated : values[n] = Combine(n, snapshot)

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

\* Round start fuses Budget's TryAllocate(1) effect with capture of the
\* snapshot used by this round's messages.
CStartRound ==
    /\ round = "idle"
    /\ changed = TRUE
    /\ b_allocated + b_reserved + b_pending + 1 <= b_capacity
    /\ b_allocated' = b_allocated + 1
    /\ snapshot' = values
    /\ updated' = {}
    /\ round' = "running"
    /\ UNCHANGED <<b_capacity, b_reserved, b_pending, values, changed>>

CUpdateNode(n) ==
    /\ round = "running"
    /\ n \notin updated
    /\ values' = [values EXCEPT ![n] = Combine(n, snapshot)]
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

\* Refinement mapping to PropagationPassGraph.
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

\* Every construction behavior must map to a PropagationPassGraph behavior,
\* including its fairness conjuncts.
PropagationPassGraphRefinement == PPG!Spec
====
