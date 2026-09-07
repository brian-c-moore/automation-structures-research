---- MODULE StateOnlyConformance_NEG ----
EXTENDS CommonSemanticSchema

Phases == {"idle", "active", "closed"}

ImplementationStates ==
    [phase : Phases, authorized : BOOLEAN, committed : BOOLEAN]

FormalStates == Phases
FormalSteps == {<<"idle", "active">>, <<"active", "closed">>}

Abstraction == [s \in ImplementationStates |-> s.phase]

BypassSteps ==
    {pair \in ImplementationStates \X ImplementationStates :
        /\ pair[1].phase = "idle"
        /\ pair[2] =
              [pair[1] EXCEPT
                  !.phase = "closed",
                  !.committed = TRUE]}

TransitionConformance ==
    StepsRefine(BypassSteps, FormalStates, FormalSteps, Abstraction)

SchemaRejectsStateOnlyMapping == ~TransitionConformance

VARIABLE state

vars == <<state>>

InitialState ==
    [phase |-> "idle", authorized |-> FALSE, committed |-> FALSE]

Init == state = InitialState

BypassCommit ==
    /\ state.phase = "idle"
    /\ state' =
          [state EXCEPT
              !.phase = "closed",
              !.committed = TRUE]

Next == BypassCommit

Spec == Init /\ [][Next]_vars

StateOnlyMapping == state.phase \in FormalStates

InheritedAuthorization == state.committed => state.authorized

====
