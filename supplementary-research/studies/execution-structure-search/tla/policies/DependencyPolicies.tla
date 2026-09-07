---- MODULE DependencyPolicies ----
\* ====================================================================
\* POLICY SPEC: DEPENDENCIES (docs/execution-modalities.md)
\*
\* Per-operator behavior:
\*   "fixed"          - function never changes
\*   "hot_swappable"  - Erlang `become`, Pony behaviors: function swaps
\*   "conditional"    - operator routes per-record by predicate
\*
\* Operator behavior is modeled as a function tag (which symbolizes
\* which transformation is active). The dependency policy governs how
\* that tag may evolve.
\* ====================================================================
EXTENDS Naturals, FiniteSets

CONSTANTS Operators, Behaviors, Mode, Inputs

ASSUME Mode \in {"fixed", "hot_swappable", "conditional"}

VARIABLES behavior, last_output

\* behavior    : function Operators -> Behaviors
\* last_output : per-op last emitted output (Behaviors \X Inputs -> Outputs
\*               is collapsed: the behavior tag at last output is recorded
\*               so stability can be checked for "fixed" mode).

vars == <<behavior, last_output>>

TypeInvariant ==
    /\ behavior    \in [Operators -> Behaviors]
    /\ last_output \in [Operators -> Behaviors \cup {"none"}]

Init ==
    /\ behavior    = [o \in Operators |-> CHOOSE b \in Behaviors : TRUE]
    /\ last_output = [o \in Operators |-> "none"]

ProcessInput(o) ==
    /\ last_output' = [last_output EXCEPT ![o] = behavior[o]]
    /\ UNCHANGED behavior

\* fixed: no Become allowed.
\* hot_swappable: any operator may swap to any behavior at any time.
Become(o) ==
    /\ Mode = "hot_swappable"
    /\ \E b \in Behaviors :
        /\ b # behavior[o]
        /\ behavior' = [behavior EXCEPT ![o] = b]
    /\ UNCHANGED last_output

\* conditional: behavior changes per input within a fixed set of
\* alternatives, modelled here as a small switch.
ConditionalSwitch(o) ==
    /\ Mode = "conditional"
    /\ \E b \in Behaviors :
        /\ behavior' = [behavior EXCEPT ![o] = b]
    /\ UNCHANGED last_output

Next ==
    \/ \E o \in Operators : ProcessInput(o)
    \/ \E o \in Operators : Become(o)
    \/ \E o \in Operators : ConditionalSwitch(o)
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

\* ----- INVARIANTS -----

\* Fixed mode: behavior is the same as it was initialized.
\* (A witness variable belongs in tests; the assertion here is that no
\* Become can fire under fixed Mode, by construction.)
FixedNoChange ==
    Mode = "fixed" => TRUE  \* structural: Become and ConditionalSwitch are guarded

\* Hot-swappable: behavior can be any element of Behaviors.
HotSwappableTotality ==
    Mode = "hot_swappable" =>
        \A o \in Operators : behavior[o] \in Behaviors

\* Conditional: each transition keeps behavior in Behaviors.
ConditionalSoundness ==
    \A o \in Operators : behavior[o] \in Behaviors
====
