---- MODULE ActuationPass_NEG_PassCompleteness ----
\* NEGATIVE CONTROL, generated. Not a specification: this is ActuationPass
\* carrying one deliberate defect, so that a checker fails on it.
\*
\*   base module      : ActuationPass
\*   mutation site    : Finish
\*   target           : PassCompleteness
\*   required outcome : with only PassCompleteness declared, TLC MUST report the invariant
\*                      violated. A run that finds no error is a control that has
\*                      stopped measuring.
\*
\* The mutation is delimited by the markers below. Outside them, and
\* apart from the module name, this file is ActuationPass verbatim, less
\* that module's commentary.

EXTENDS FiniteSets

CONSTANTS Seats, Resources, NULL

VARIABLES allocation,
          effects,
          complete

vars == <<allocation, effects, complete>>

Actuated == {s \in Seats : effects[s] /= NULL}

TypeInvariant ==
    /\ allocation \in [Seats -> Resources \cup {NULL}]
    /\ effects    \in [Seats -> Resources \cup {NULL}]
    /\ complete   \in BOOLEAN

ActuationScope ==
    \A s \in Actuated : allocation[s] /= NULL

EffectFidelity ==
    \A s \in Seats : effects[s] /= NULL => effects[s] = allocation[s]

PassCompleteness ==
    complete => \A s \in Seats : allocation[s] /= NULL => effects[s] /= NULL

Init ==
    /\ allocation \in [Seats -> Resources \cup {NULL}]
    /\ effects = [s \in Seats |-> NULL]
    /\ complete = FALSE

Actuate(s) ==
    /\ ~complete
    /\ effects[s] = NULL
    /\ allocation[s] /= NULL
    /\ effects' = [effects EXCEPT ![s] = allocation[s]]
    /\ UNCHANGED <<allocation, complete>>

Allocate(s, r) ==
    /\ ~complete
    /\ allocation[s] = NULL
    /\ allocation' = [allocation EXCEPT ![s] = r]
    /\ UNCHANGED <<effects, complete>>

Deallocate(s) ==
    /\ ~complete
    /\ allocation[s] /= NULL
    /\ effects[s] = NULL
    /\ allocation' = [allocation EXCEPT ![s] = NULL]
    /\ UNCHANGED <<effects, complete>>

\* ---- MUTATION BEGINS -- to the closing marker, this replaces the base text.
Finish ==
    /\ ~complete
    /\ complete' = TRUE
\* ---- MUTATION ENDS.
    /\ UNCHANGED <<allocation, effects>>

Next ==
    \/ \E s \in Seats : Actuate(s)
    \/ \E s \in Seats, r \in Resources : Allocate(s, r)
    \/ \E s \in Seats : Deallocate(s)
    \/ Finish

Spec == Init /\ [][Next]_vars

====
