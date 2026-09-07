---- MODULE CheckActUnstableInterference_NEG ----
EXTENDS TheoryKernel

States ==
    [phase : {"idle", "checked", "committed"},
     predicate_held : BOOLEAN]

CheckResultStates ==
    {s \in States : s.phase = "checked" /\ s.predicate_held}

PredicateStates == {s \in States : s.predicate_held}

InterferenceSteps ==
    {pair \in States \X States :
        /\ pair[1].phase = "checked"
        /\ pair[1].predicate_held
        /\ pair[2] = [pair[1] EXCEPT !.predicate_held = FALSE]}

GovernedCommitSteps ==
    {pair \in States \X States :
        /\ pair[1].phase = "checked"
        /\ pair[2] = [pair[1] EXCEPT !.phase = "committed"]}

SchemaRejectsUnstableInterference ==
    ~StableCheckActPremises(
        States, CheckResultStates, PredicateStates,
        InterferenceSteps, GovernedCommitSteps)

VARIABLE state

vars == <<state>>

Init ==
    state = [phase |-> "idle", predicate_held |-> FALSE]

Check ==
    /\ state.phase = "idle"
    /\ state' = [phase |-> "checked", predicate_held |-> TRUE]

Interfere ==
    /\ state.phase = "checked"
    /\ state.predicate_held
    /\ state' = [state EXCEPT !.predicate_held = FALSE]

Commit ==
    /\ state.phase = "checked"
    /\ state' = [state EXCEPT !.phase = "committed"]

Next == Check \/ Interfere \/ Commit

Spec == Init /\ [][Next]_vars

CheckedPredicateStable ==
    state.phase # "checked" \/ state.predicate_held

====
