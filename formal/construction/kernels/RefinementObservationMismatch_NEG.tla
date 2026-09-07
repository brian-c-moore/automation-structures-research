---- MODULE RefinementObservationMismatch_NEG ----
EXTENDS RefinementKernel, TLC

FormalStates == {"open", "closed"}
ImplementationStates == {"i-open", "i-closed"}
FormalSteps == {<<"open", "closed">>}
ImplementationSteps == {<<"i-open", "i-closed">>}

Abstraction ==
    [s \in ImplementationStates |->
        IF s = "i-open" THEN "open" ELSE "closed"]

ObservationDomain == {"open-view", "closed-view", "wrong-view"}
AllowedObservations == {"open-view", "closed-view"}
FormalObserve ==
    [s \in FormalStates |->
        IF s = "open" THEN "open-view" ELSE "closed-view"]
ImplementationObserve ==
    [s \in ImplementationStates |->
        IF s = "i-open" THEN "open-view" ELSE "wrong-view"]

StepConformance ==
    StepsRefine(
        ImplementationSteps, FormalStates, FormalSteps, Abstraction)

SchemaRejectsObservationMismatch ==
    ~ObservationsAgree(
        ImplementationStates, ImplementationObserve,
        FormalObserve, Abstraction)

VARIABLE state

vars == <<state, progressState>>

Init ==
    /\ state = "i-open"
    /\ progressState = "unused"

Advance ==
    /\ state = "i-open"
    /\ state' = "i-closed"
    /\ UNCHANGED progressState

Next == Advance \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

InheritedAllowedObservation ==
    ImplementationObserve[state] \in AllowedObservations

====
