---- MODULE RefinementMappingRejections ----
EXTENDS RefinementKernel, TLC

FormalStates == {"open", "closed", "bad"}
ImplementationStates == {"i-open", "i-closed", "i-bad"}

Abstraction ==
    [s \in ImplementationStates |->
        CASE s = "i-open" -> "open"
          [] s = "i-closed" -> "closed"
          [] OTHER -> "bad"]

FormalSteps == {<<"open", "closed">>}
WrongImplementationStep == {<<"i-open", "i-bad">>}
WrongImplementationFailure == {<<"i-open", "i-bad">>}
FormalFailureSteps == {}

RejectsWrongInitialization ==
    ~InitialStatesRefine({"i-bad"}, {"open"}, Abstraction)

RejectsWrongStep ==
    ~StepsRefine(
        WrongImplementationStep,
        FormalStates, FormalSteps, Abstraction)

RejectsWrongFailure ==
    ~StepsRefineWithoutStutter(
        WrongImplementationFailure,
        FormalFailureSteps, Abstraction)

VARIABLE state

vars == <<state, progressState>>

Init ==
    /\ state = "i-open"
    /\ progressState = "unused"

Next == UNCHANGED vars

Spec == Init /\ [][Next]_vars

====
