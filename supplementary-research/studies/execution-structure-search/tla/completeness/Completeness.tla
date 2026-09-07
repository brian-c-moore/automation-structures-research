---- MODULE Completeness ----
\* ====================================================================
\* COMPLETENESS SPEC (docs/execution-modalities.md)
\*
\* The parameterized generic execution. Modality is a CONSTANT and the
\* ASSUME below pins it to one of the four, so a run is one modality's
\* state machine: each named action is guarded by Modality.
\*
\* WHAT A RUN ESTABLISHES. FourModalitiesExhaustive is a conjunction of
\* four implications, each guarded by Modality = "X". One value is bound
\* per run, so one conjunct has a true antecedent and the other three
\* hold vacuously, and what the run checks is the closure condition of
\* the modality it was configured with. It asserts no classification of
\* a state into a modality and no exclusivity between the four.
\*
\* Not modelled here: there is no search for behaviors expressible in the
\* union of the four and in no single one, and nothing in this module
\* compares behaviors across values of Modality. The verification does not
\* establish the four-modality count as complete in an absolute sense.
\* ====================================================================
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Units, Modality

\* Units    : finite set of work-unit identifiers
\* Modality : one of "Sequential", "ForkJoin", "StepGraph", "StreamGraph"

ASSUME Modality \in {"Sequential", "ForkJoin", "StepGraph", "StreamGraph"}

ExecutionStates == {"unborn", "active", "completed"}

VARIABLES
    ustate,        \* per-unit state
    queue_depth,   \* abstract: total work in the pipeline (StreamGraph)
    barrier_phase  \* abstract phase counter (ForkJoin)

vars == <<ustate, queue_depth, barrier_phase>>

TypeInvariant ==
    /\ ustate        \in [Units -> ExecutionStates]
    /\ queue_depth   \in 0..Cardinality(Units)
    /\ barrier_phase \in {"fork", "join", "done"}

Init ==
    /\ ustate        = [u \in Units |-> "unborn"]
    /\ queue_depth   = 0
    /\ barrier_phase = "fork"

\* ----- Sequential modality: at most one active unit -----
SeqStartUnit(u) ==
    /\ Modality = "Sequential"
    /\ ustate[u] = "unborn"
    /\ \A v \in Units : ustate[v] # "active"
    /\ ustate' = [ustate EXCEPT ![u] = "active"]
    /\ UNCHANGED <<queue_depth, barrier_phase>>

SeqCompleteUnit(u) ==
    /\ Modality = "Sequential"
    /\ ustate[u] = "active"
    /\ ustate' = [ustate EXCEPT ![u] = "completed"]
    /\ UNCHANGED <<queue_depth, barrier_phase>>

\* ----- ForkJoin modality: any units active concurrently, barrier -----
ForkStartUnit(u) ==
    /\ Modality = "ForkJoin"
    /\ barrier_phase = "fork"
    /\ ustate[u] = "unborn"
    /\ ustate' = [ustate EXCEPT ![u] = "active"]
    /\ UNCHANGED <<queue_depth, barrier_phase>>

ForkCompleteUnit(u) ==
    /\ Modality = "ForkJoin"
    /\ barrier_phase = "fork"
    /\ ustate[u] = "active"
    /\ ustate' = [ustate EXCEPT ![u] = "completed"]
    /\ UNCHANGED <<queue_depth, barrier_phase>>

ForkBarrier ==
    /\ Modality = "ForkJoin"
    /\ barrier_phase = "fork"
    /\ \A u \in Units : ustate[u] = "completed"
    /\ barrier_phase' = "done"
    /\ UNCHANGED <<ustate, queue_depth>>

\* ----- StepGraph modality: completions cascade -----
StepStartUnit(u) ==
    /\ Modality = "StepGraph"
    /\ ustate[u] = "unborn"
    /\ ustate' = [ustate EXCEPT ![u] = "active"]
    /\ UNCHANGED <<queue_depth, barrier_phase>>

StepCompleteUnit(u) ==
    /\ Modality = "StepGraph"
    /\ ustate[u] = "active"
    /\ ustate' = [ustate EXCEPT ![u] = "completed"]
    /\ UNCHANGED <<queue_depth, barrier_phase>>

\* ----- StreamGraph modality: records flow through queues -----
StreamIngest ==
    /\ Modality = "StreamGraph"
    /\ queue_depth < Cardinality(Units)
    /\ queue_depth' = queue_depth + 1
    /\ UNCHANGED <<ustate, barrier_phase>>

StreamDrain ==
    /\ Modality = "StreamGraph"
    /\ queue_depth > 0
    /\ queue_depth' = queue_depth - 1
    /\ UNCHANGED <<ustate, barrier_phase>>

\* ----- Generic dispatch -----
Next ==
    \/ \E u \in Units :
        \/ SeqStartUnit(u) \/ SeqCompleteUnit(u)
        \/ ForkStartUnit(u) \/ ForkCompleteUnit(u)
        \/ StepStartUnit(u) \/ StepCompleteUnit(u)
    \/ ForkBarrier
    \/ StreamIngest
    \/ StreamDrain
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

\* ----- CLOSURE INVARIANT -----
\* Every reachable state belongs to the modality chosen in CONSTANTS.
\* The classifier:
\*   - Sequential : at most one active unit ever
\*   - ForkJoin   : multiple active, all completed before barrier_phase = done
\*   - StepGraph  : multiple active possible, completions monotone
\*   - StreamGraph: queue_depth nonzero possible

ActiveCount == Cardinality({u \in Units : ustate[u] = "active"})

\* In Sequential mode, at most one active unit.
SeqClosure ==
    Modality = "Sequential" => ActiveCount <= 1

\* In ForkJoin mode, barrier_phase = done implies all completed.
ForkJoinClosure ==
    Modality = "ForkJoin" =>
        (barrier_phase = "done" => \A u \in Units : ustate[u] = "completed")

\* In StepGraph mode, every unit's state is one of the three execution
\* states. Monotonicity of completion is a two-state property and is not
\* what this predicate says.
StepGraphClosure ==
    Modality = "StepGraph" =>
        \A u \in Units : ustate[u] \in ExecutionStates

\* In StreamGraph mode, queue depth is bounded.
StreamGraphClosure ==
    Modality = "StreamGraph" =>
        queue_depth <= Cardinality(Units)

\* The conjunction of the four closure conditions. At a given Modality
\* one conjunct is live and three are vacuous; joint exhaustiveness of
\* the four modalities is not what this predicate states.
FourModalitiesExhaustive ==
    /\ SeqClosure
    /\ ForkJoinClosure
    /\ StepGraphClosure
    /\ StreamGraphClosure
====
