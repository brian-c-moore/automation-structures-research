---- MODULE ForkJoinRefinesStepGraph ----
\* ForkJoin refines StepGraph under an encoding with one source, parallel
\* anonymous workers, one sink, and barrier semantics.
\*
\* Nodes are integers 0 (Source), WorkerIds (workers), and 100 (Sink).
\* The refinement-mapping function takes phase and wstate as
\* explicit arguments rather than referencing state variables, so it
\* can be evaluated on either the current or primed state without
\* relying on TLC's nullary-operator priming.
EXTENDS Naturals, FiniteSets

CONSTANTS WorkerIds

Source == 0
Sink   == 100
SGNodes == {Source, Sink} \cup WorkerIds
SGEdges ==
    { <<Source, w>> : w \in WorkerIds }
    \cup { <<w, Sink>> : w \in WorkerIds }

VARIABLES wstate, phase, output_ready, sgstate

vars == <<wstate, phase, output_ready, sgstate>>

WorkerStates == {"ready", "running", "complete"}
Phases       == {"fork", "join", "done"}
SGStates     == {"NotReady", "Ready", "Running", "Completed"}

TypeInvariant ==
    /\ wstate       \in [WorkerIds -> WorkerStates]
    /\ phase        \in Phases
    /\ output_ready \in BOOLEAN
    /\ sgstate      \in [SGNodes -> SGStates]

\* Parameterized refinement mapping.
SinkMapOf(p) ==
    CASE p = "fork" -> "NotReady"
      [] p = "join" -> "Running"
      [] p = "done" -> "Completed"

WorkerMapOf(ws, w) ==
    CASE ws[w] = "ready"    -> "Ready"
      [] ws[w] = "running"  -> "Running"
      [] ws[w] = "complete" -> "Completed"

ExpectedSGOf(p, ws) ==
    [n \in SGNodes |->
        IF n = Source THEN "Completed"
        ELSE IF n = Sink THEN SinkMapOf(p)
        ELSE WorkerMapOf(ws, n)]

\* sgstate's initial value is the refinement-mapping function
\* ExpectedSGOf applied at the initial phase and worker states, not a
\* literal function value, which is what makes the RefinementMapping
\* invariant trivial at Init.
Init ==
    /\ wstate       = [w \in WorkerIds |-> "ready"]
    /\ phase        = "fork"
    /\ output_ready = FALSE
    /\ sgstate      = ExpectedSGOf("fork", [w \in WorkerIds |-> "ready"])

StartWorker(w) ==
    /\ phase = "fork"
    /\ wstate[w] = "ready"
    /\ wstate' = [wstate EXCEPT ![w] = "running"]
    /\ sgstate' = ExpectedSGOf(phase, [wstate EXCEPT ![w] = "running"])
    /\ UNCHANGED <<phase, output_ready>>

CompleteWorker(w) ==
    /\ phase = "fork"
    /\ wstate[w] = "running"
    /\ wstate' = [wstate EXCEPT ![w] = "complete"]
    /\ sgstate' = ExpectedSGOf(phase, [wstate EXCEPT ![w] = "complete"])
    /\ UNCHANGED <<phase, output_ready>>

AllComplete == \A w \in WorkerIds : wstate[w] = "complete"

Barrier ==
    /\ phase = "fork"
    /\ AllComplete
    /\ phase'   = "join"
    /\ sgstate' = ExpectedSGOf("join", wstate)
    /\ UNCHANGED <<wstate, output_ready>>

ProduceOutput ==
    /\ phase = "join"
    /\ output_ready' = TRUE
    /\ phase'        = "done"
    /\ sgstate'      = ExpectedSGOf("done", wstate)
    /\ UNCHANGED wstate

Next ==
    \/ \E w \in WorkerIds : StartWorker(w) \/ CompleteWorker(w)
    \/ Barrier
    \/ ProduceOutput
    \/ (phase = "done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

RefinementMapping == sgstate = ExpectedSGOf(phase, wstate)

PredecessorsOf(n) == {p \in SGNodes : <<p, n>> \in SGEdges}

NoRunBeforePredecessors ==
    \A n \in SGNodes :
        (sgstate[n] \in {"Running", "Completed"}) =>
            \A p \in PredecessorsOf(n) : sgstate[p] = "Completed"
====
