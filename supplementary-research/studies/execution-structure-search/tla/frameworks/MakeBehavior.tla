---- MODULE MakeBehavior ----
\* ====================================================================
\* MAKE BEHAVIORAL SPEC (bounded study configuration)
\*
\* Behavioral property under the StepGraph modality state machine:
\* a configuration with no dirty inputs produces zero rebuilds.
\*
\* Modeled state machine:
\*   - inputs each carry a `dirty` flag
\*   - external events flip an input from clean to dirty
\*   - a `RunMake` action observes the dirty set and either
\*       * rebuilds all dirty inputs (clearing flags, incrementing
\*         rebuild_count), if any input is dirty, or
\*       * is a no-op if all inputs are clean.
\*
\* Invariant `NoRebuildsWhenClean` is an action property: rebuild_count
\* increases only when at least one input was dirty in the pre-state.
\* ====================================================================
EXTENDS Naturals, FiniteSets

CONSTANTS Inputs, MaxRuns

VARIABLES dirty, rebuild_count, runs

vars == <<dirty, rebuild_count, runs>>

TypeInvariant ==
    /\ dirty         \in [Inputs -> BOOLEAN]
    /\ rebuild_count \in 0..MaxRuns
    /\ runs          \in 0..MaxRuns

Init ==
    /\ dirty         = [i \in Inputs |-> FALSE]
    /\ rebuild_count = 0
    /\ runs          = 0

\* External event: an input becomes dirty (e.g. file edited).
MarkDirty(i) ==
    /\ runs < MaxRuns
    /\ ~dirty[i]
    /\ dirty' = [dirty EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<rebuild_count, runs>>

\* `make` invocation: rebuild iff at least one input is dirty.
RunMake ==
    /\ runs < MaxRuns
    /\ runs' = runs + 1
    /\ IF \E i \in Inputs : dirty[i]
       THEN /\ dirty'         = [i \in Inputs |-> FALSE]
            /\ rebuild_count' = rebuild_count + 1
       ELSE UNCHANGED <<dirty, rebuild_count>>

DoneStuttering ==
    /\ runs >= MaxRuns
    /\ UNCHANGED vars

Next ==
    \/ \E i \in Inputs : MarkDirty(i)
    \/ RunMake
    \/ DoneStuttering

Spec == Init /\ [][Next]_vars

\* ----- BEHAVIORAL INVARIANT -----
\* If rebuild_count increases by one in a step, at least one input was
\* dirty in the pre-state. Equivalently: a clean configuration cannot
\* produce a rebuild.
NoRebuildsWhenClean ==
    [][rebuild_count' = rebuild_count + 1 => \E i \in Inputs : dirty[i]]_vars
====
