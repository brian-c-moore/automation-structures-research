---- MODULE LifecyclePolicies ----
\* ====================================================================
\* POLICY SPEC: LIFECYCLE (docs/execution-modalities.md)
\*
\* Worker lifecycle policies:
\*   "simple"        - spawn / run / terminate
\*   "supervision"   - supervisor restarts crashed children
\*   "checkpoint"    - checkpoint state, restart from last checkpoint
\*   "drain"         - stop accepting new work, complete inflight, exit
\*
\* Bounded `restarts` and a global `steps` counter keep the state
\* space finite; without them the crash-restart cycle is unbounded.
\* ====================================================================
EXTENDS Naturals, FiniteSets

CONSTANTS Workers, Mode, MaxCheckpoints, MaxRestarts, MaxSteps

ASSUME Mode \in {"simple", "supervision", "checkpoint", "drain"}

WorkerStates == {"unspawned", "running", "crashed", "checkpointed",
                 "draining", "terminated"}

VARIABLES wstate, checkpoints, restarts, draining, steps

vars == <<wstate, checkpoints, restarts, draining, steps>>

TypeInvariant ==
    /\ wstate      \in [Workers -> WorkerStates]
    /\ checkpoints \in [Workers -> 0..MaxCheckpoints]
    /\ restarts    \in [Workers -> 0..MaxRestarts]
    /\ draining    \in BOOLEAN
    /\ steps       \in 0..MaxSteps

Init ==
    /\ wstate      = [w \in Workers |-> "unspawned"]
    /\ checkpoints = [w \in Workers |-> 0]
    /\ restarts    = [w \in Workers |-> 0]
    /\ draining    = FALSE
    /\ steps       = 0

StepBound == steps < MaxSteps

BumpStep == steps' = steps + 1

Spawn(w) ==
    /\ StepBound
    /\ wstate[w] = "unspawned"
    /\ ~draining
    /\ wstate' = [wstate EXCEPT ![w] = "running"]
    /\ BumpStep
    /\ UNCHANGED <<checkpoints, restarts, draining>>

Crash(w) ==
    /\ StepBound
    /\ wstate[w] = "running"
    /\ wstate' = [wstate EXCEPT ![w] = "crashed"]
    /\ BumpStep
    /\ UNCHANGED <<checkpoints, restarts, draining>>

SupervisedRestart(w) ==
    /\ StepBound
    /\ Mode = "supervision"
    /\ wstate[w] = "crashed"
    /\ restarts[w] < MaxRestarts
    /\ wstate'   = [wstate EXCEPT ![w] = "running"]
    /\ restarts' = [restarts EXCEPT ![w] = restarts[w] + 1]
    /\ BumpStep
    /\ UNCHANGED <<checkpoints, draining>>

Checkpoint(w) ==
    /\ StepBound
    /\ Mode = "checkpoint"
    /\ wstate[w] = "running"
    /\ checkpoints[w] < MaxCheckpoints
    /\ checkpoints' = [checkpoints EXCEPT ![w] = checkpoints[w] + 1]
    /\ wstate'      = [wstate EXCEPT ![w] = "checkpointed"]
    /\ BumpStep
    /\ UNCHANGED <<restarts, draining>>

CheckpointRestart(w) ==
    /\ StepBound
    /\ Mode = "checkpoint"
    /\ wstate[w] \in {"checkpointed", "crashed"}
    /\ checkpoints[w] > 0
    /\ restarts[w] < MaxRestarts
    /\ wstate'   = [wstate EXCEPT ![w] = "running"]
    /\ restarts' = [restarts EXCEPT ![w] = restarts[w] + 1]
    /\ BumpStep
    /\ UNCHANGED <<checkpoints, draining>>

StartDrain ==
    /\ StepBound
    /\ Mode = "drain"
    /\ ~draining
    /\ draining' = TRUE
    /\ BumpStep
    /\ UNCHANGED <<wstate, checkpoints, restarts>>

DrainWorker(w) ==
    /\ StepBound
    /\ Mode = "drain"
    /\ draining
    /\ wstate[w] = "running"
    /\ wstate' = [wstate EXCEPT ![w] = "draining"]
    /\ BumpStep
    /\ UNCHANGED <<checkpoints, restarts, draining>>

CompleteDrain(w) ==
    /\ StepBound
    /\ wstate[w] = "draining"
    /\ wstate'   = [wstate EXCEPT ![w] = "terminated"]
    /\ BumpStep
    /\ UNCHANGED <<checkpoints, restarts, draining>>

Terminate(w) ==
    /\ StepBound
    /\ Mode = "simple"
    /\ wstate[w] = "running"
    /\ wstate'   = [wstate EXCEPT ![w] = "terminated"]
    /\ BumpStep
    /\ UNCHANGED <<checkpoints, restarts, draining>>

Next ==
    \/ \E w \in Workers :
        \/ Spawn(w) \/ Crash(w)
        \/ SupervisedRestart(w)
        \/ Checkpoint(w) \/ CheckpointRestart(w)
        \/ DrainWorker(w) \/ CompleteDrain(w)
        \/ Terminate(w)
    \/ StartDrain
    \/ (steps >= MaxSteps /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

ValidStates == \A w \in Workers : wstate[w] \in WorkerStates

SimpleNoRestart ==
    Mode = "simple" => \A w \in Workers : restarts[w] = 0

CheckpointsBounded ==
    \A w \in Workers : checkpoints[w] <= MaxCheckpoints

RestartsBounded ==
    \A w \in Workers : restarts[w] <= MaxRestarts
====
