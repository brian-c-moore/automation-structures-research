---- MODULE OperatorStates ----
\* ====================================================================
\* SHARED PRIMITIVE: OPERATOR STATE MACHINE
\*
\* An operator lifecycle state set and its ordering, written as a
\* shared module. No module under Execution Modalities extends or
\* instantiates this one: each of the four modality specs declares the
\* states it needs itself, and StepGraph defines its own NodeStates and
\* Rank rather than take these.
\*
\* Operator lifecycle states:
\*   NotReady  : preconditions for execution not met
\*   Ready     : eligible to run
\*   Running   : currently executing
\*   Completed : terminal state (used by StepGraph, ForkJoin)
\*   Idle      : between firings (used by StreamGraph)
\*   Processing: currently processing one record (StreamGraph)
\* ====================================================================
EXTENDS Naturals

AllStates == {"NotReady", "Ready", "Running", "Completed", "Idle", "Processing"}

\* Rank operators by progress, used to express monotonic-progress
\* invariants in StepGraph and ForkJoin.
Rank(s) ==
    CASE s = "NotReady"   -> 0
      [] s = "Ready"      -> 1
      [] s = "Running"    -> 2
      [] s = "Completed"  -> 3
      [] s = "Idle"       -> 0
      [] s = "Processing" -> 1
      [] OTHER            -> 0

\* Valid transitions for completion-bounded modalities (StepGraph, ForkJoin).
CompletionTransitions ==
    { <<"NotReady", "Ready">>
    , <<"Ready",    "Running">>
    , <<"Running",  "Completed">>
    }

\* Valid transitions for streaming modalities (StreamGraph).
StreamingTransitions ==
    { <<"Idle",       "Processing">>
    , <<"Processing", "Idle">>
    }
====
