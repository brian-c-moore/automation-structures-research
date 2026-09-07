---- MODULE AirflowBehavior ----
\* ====================================================================
\* AIRFLOW BEHAVIORAL SPEC (bounded study configuration)
\*
\* Behavioral property under the StepGraph modality state machine:
\* a task transitions to Running only after all of its upstream
\* dependencies are marked Success.
\* ====================================================================
EXTENDS Naturals, FiniteSets

\* Four-task DAG:
\*   ingest -> {transform_a, transform_b} -> aggregate
Tasks == {"ingest", "transform_a", "transform_b", "aggregate"}

Upstream ==
    [t \in Tasks |->
        CASE t = "ingest"      -> {}
          [] t = "transform_a" -> {"ingest"}
          [] t = "transform_b" -> {"ingest"}
          [] t = "aggregate"   -> {"transform_a", "transform_b"}]

TaskStates == {"NotReady", "Queued", "Running", "Success"}

VARIABLES tstate

vars == <<tstate>>

TypeInvariant == tstate \in [Tasks -> TaskStates]

Init ==
    tstate = [t \in Tasks |->
                IF Upstream[t] = {} THEN "Queued" ELSE "NotReady"]

\* Become Queued: all upstream tasks Success.
Queue(t) ==
    /\ tstate[t] = "NotReady"
    /\ Upstream[t] # {}
    /\ \A u \in Upstream[t] : tstate[u] = "Success"
    /\ tstate' = [tstate EXCEPT ![t] = "Queued"]

StartRun(t) ==
    /\ tstate[t] = "Queued"
    /\ tstate' = [tstate EXCEPT ![t] = "Running"]

Complete(t) ==
    /\ tstate[t] = "Running"
    /\ tstate' = [tstate EXCEPT ![t] = "Success"]

AllDone == \A t \in Tasks : tstate[t] = "Success"

Next ==
    \/ \E t \in Tasks : Queue(t) \/ StartRun(t) \/ Complete(t)
    \/ AllDone /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars

\* ----- BEHAVIORAL INVARIANT -----
\* No task is Running or Success unless every upstream task is Success.
DependencyCompletionOrdering ==
    \A t \in Tasks :
        tstate[t] \in {"Running", "Success"} =>
            \A u \in Upstream[t] : tstate[u] = "Success"
====
