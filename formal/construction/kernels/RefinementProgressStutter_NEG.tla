---- MODULE RefinementProgressStutter_NEG ----
EXTENDS RefinementKernel, TLC

FormalStates == {"open", "closed"}
ImplementationStates == {"i-open", "i-spin"}
FormalProgressSteps == {<<"open", "closed">>}
ImplementationProgressSteps ==
    {<<"i-open", "i-spin">>, <<"i-spin", "i-spin">>}

Abstraction ==
    [s \in ImplementationStates |-> "open"]

StepMappingAllowsStutter ==
    StepsRefine(
        ImplementationProgressSteps,
        FormalStates, FormalProgressSteps, Abstraction)

ProgressMappingRejectsStutter ==
    ~StepsRefineWithoutStutter(
        ImplementationProgressSteps,
        FormalProgressSteps, Abstraction)

ImplementationClosedStates ==
    ConcreteClosedStates(
        ImplementationStates, {"closed"}, Abstraction)

Init == progressState = "i-open"

Spin ==
    \/ /\ progressState = "i-open"
       /\ progressState' = "i-spin"
    \/ /\ progressState = "i-spin"
       /\ progressState' = "i-spin"

Spec ==
    /\ Init
    /\ [][Spin]_progressVars
    /\ WF_progressVars(Spin)

EventualImplementationClosure ==
    <> (progressState \in ImplementationClosedStates)

====
