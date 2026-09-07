---- MODULE ForkJoin ----
\* Fork-join carrier: workers advance independently, all workers synchronize
\* at one barrier, and output is published from the completed worker snapshot.
\* The carrier checks barrier completeness, output consistency, and phase
\* ordering. It does not represent inter-worker communication during the
\* parallel phase.
EXTENDS Naturals, FiniteSets

CONSTANTS Workers, ValueDomain
\* Workers     : finite set of worker identifiers
\* ValueDomain : finite set of possible per-worker values

\* Init seeds both value functions with CHOOSE over ValueDomain, and CHOOSE over
\* an empty set is not defined, so the non-emptiness the module relies on is
\* stated here rather than left to whichever model binds the constant.
ASSUME ValueDomainNonEmpty == ValueDomain # {}

VARIABLES wstate, wvalue, phase, output_ready, output_snapshot

vars == <<wstate, wvalue, phase, output_ready, output_snapshot>>

WorkerStates == {"ready", "running", "complete"}
Phases       == {"fork", "join", "done"}

TypeInvariant ==
    /\ wstate          \in [Workers -> WorkerStates]
    /\ wvalue          \in [Workers -> ValueDomain]
    /\ phase           \in Phases
    /\ output_ready    \in BOOLEAN
    /\ output_snapshot \in [Workers -> ValueDomain]

Init ==
    /\ wstate          = [w \in Workers |-> "ready"]
    /\ wvalue          = [w \in Workers |-> CHOOSE v \in ValueDomain : TRUE]
    /\ phase           = "fork"
    /\ output_ready    = FALSE
    /\ output_snapshot = [w \in Workers |-> CHOOSE v \in ValueDomain : TRUE]

\* A worker begins execution. Workers proceed independently — no edges.
StartWorker(w) ==
    /\ phase = "fork"
    /\ wstate[w] = "ready"
    /\ wstate' = [wstate EXCEPT ![w] = "running"]
    /\ UNCHANGED <<wvalue, phase, output_ready, output_snapshot>>

\* A worker finishes and produces its value. No communication with peers.
CompleteWorker(w) ==
    /\ phase = "fork"
    /\ wstate[w] = "running"
    /\ \E v \in ValueDomain :
        /\ wvalue' = [wvalue EXCEPT ![w] = v]
    /\ wstate' = [wstate EXCEPT ![w] = "complete"]
    /\ UNCHANGED <<phase, output_ready, output_snapshot>>

AllComplete == \A w \in Workers : wstate[w] = "complete"

\* Synchronization barrier: all workers complete before join phase.
Barrier ==
    /\ phase = "fork"
    /\ AllComplete
    /\ phase' = "join"
    /\ UNCHANGED <<wstate, wvalue, output_ready, output_snapshot>>

\* Aggregate output. The output is a snapshot of all worker values.
ProduceOutput ==
    /\ phase = "join"
    /\ output_snapshot' = wvalue
    /\ output_ready'    = TRUE
    /\ phase'           = "done"
    /\ UNCHANGED <<wstate, wvalue>>

DoneStuttering ==
    /\ phase = "done"
    /\ UNCHANGED vars

Next ==
    \/ \E w \in Workers : StartWorker(w) \/ CompleteWorker(w)
    \/ Barrier
    \/ ProduceOutput
    \/ DoneStuttering

Spec == Init /\ [][Next]_vars

\* The specification models only each worker's own state; no action can read
\* another worker's value during phase = "fork". This is enforced
\* structurally: CompleteWorker reads only its own slot. Inter-worker
\* isolation is therefore a representation ceiling, not a checked invariant.
\*
\* A model with a shared channel, or with CompleteWorker permitted to read
\* wvalue[other], could make this property falsifiable. This carrier has no such
\* transition, so the property remains an explicit representation ceiling and
\* is not listed as an invariant in ForkJoin.cfg.

\* Output is produced only after
\* every worker has reached the terminal state.
BarrierCompleteness ==
    output_ready => AllComplete

\* If output is ready, the snapshot is consistent with wvalue.
OutputConsistency ==
    output_ready => (output_snapshot = wvalue)

\* Phase order: "fork" precedes "join", which precedes "done".
PhaseOrdering ==
    /\ (phase = "join" => AllComplete)
    /\ (phase = "done" => output_ready)
====
