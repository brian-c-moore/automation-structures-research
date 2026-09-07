---- MODULE RefinementKernelWitness ----
EXTENDS RefinementKernel, TLC

FormalStates == {"open", "closed", "bad"}
ImplementationStates == {"i-open", "i-closed", "i-bad"}

FormalInitial == {"open"}
ImplementationInitial == {"i-open"}
FormalSafeStates == {"open", "closed"}

FormalProgressSteps ==
    {<<"open", "closed">>, <<"bad", "closed">>}
FormalOtherSteps == {<<"closed", "closed">>}
FormalSteps == FormalProgressSteps \cup FormalOtherSteps

ImplementationProgressSteps ==
    {<<"i-open", "i-closed">>, <<"i-bad", "i-closed">>}
ImplementationOtherSteps == {<<"i-closed", "i-closed">>}
ImplementationSteps ==
    ImplementationProgressSteps \cup ImplementationOtherSteps

Abstraction ==
    [s \in ImplementationStates |->
        CASE s = "i-open" -> "open"
          [] s = "i-closed" -> "closed"
          [] OTHER -> "bad"]

ObservationDomain == {"open-view", "closed-view", "bad-view"}
AllowedObservations == {"open-view", "closed-view"}
FormalObservationStates == FormalSafeStates

FormalObserve ==
    [s \in FormalStates |->
        CASE s = "open" -> "open-view"
          [] s = "closed" -> "closed-view"
          [] OTHER -> "bad-view"]

ImplementationObserve ==
    [s \in ImplementationStates |-> FormalObserve[Abstraction[s]]]

FormalClosedStates == {"closed"}
ImplementationClosedStates == {"i-closed"}
ImplementationActiveStates ==
    ImplementationStates \ ImplementationClosedStates

RankBound == 1
FormalRank ==
    [s \in FormalStates |-> IF s = "closed" THEN 0 ELSE 1]
ImplementationRank ==
    LiftedRank(ImplementationStates, Abstraction, FormalRank)

FairnessOwners == {"runtime"}
FairnessOwner == "runtime"
FormalFairnessOwnerOf ==
    [step \in FormalProgressSteps |-> FairnessOwner]
ImplementationFairnessOwnerOf ==
    [step \in ImplementationProgressSteps |-> FairnessOwner]
SelectedClasses == RefinementClasses

SafetyPremises ==
    SafetyRefinementPremises(
        ImplementationStates, FormalStates,
        ImplementationInitial, FormalInitial,
        ImplementationSteps, FormalSteps,
        FormalSafeStates, ObservationDomain,
        Abstraction, ImplementationObserve, FormalObserve)

SafetyConclusion ==
    SafetyRefinementConclusion(
        ImplementationStates, ImplementationInitial,
        ImplementationSteps, FormalSafeStates, Abstraction)

ObservationPremises ==
    ObservationPropertyPremises(
        ImplementationStates, FormalStates,
        FormalObservationStates, ObservationDomain,
        AllowedObservations, Abstraction,
        ImplementationObserve, FormalObserve)

ObservationConclusion ==
    ObservationPropertyConclusion(
        ImplementationStates, FormalObservationStates,
        AllowedObservations, Abstraction,
        ImplementationObserve)

LivenessPremises ==
    LivenessRefinementPremises(
        ImplementationStates, ImplementationActiveStates,
        ImplementationClosedStates, FormalStates,
        FormalClosedStates, FormalProgressSteps, FormalOtherSteps,
        ImplementationSteps, ImplementationProgressSteps,
        ImplementationOtherSteps,
        RankBound, FormalRank, ImplementationRank, Abstraction,
        FairnessOwners, FairnessOwner,
        FormalFairnessOwnerOf, ImplementationFairnessOwnerOf)

ImplementationStepsWithUnmappedDivergence ==
    ImplementationSteps \cup {<<"i-open", "i-bad">>}

RejectsIncompleteLivenessStepPartition ==
    ~LivenessRefinementPremises(
        ImplementationStates, ImplementationActiveStates,
        ImplementationClosedStates, FormalStates,
        FormalClosedStates, FormalProgressSteps, FormalOtherSteps,
        ImplementationStepsWithUnmappedDivergence,
        ImplementationProgressSteps, ImplementationOtherSteps,
        RankBound, FormalRank, ImplementationRank, Abstraction,
        FairnessOwners, FairnessOwner,
        FormalFairnessOwnerOf, ImplementationFairnessOwnerOf)

Init == progressState = "i-open"

ProgressAction ==
    \/ /\ progressState = "i-open"
       /\ progressState' = "i-closed"
    \/ /\ progressState = "i-bad"
       /\ progressState' = "i-closed"

OtherAction ==
    /\ progressState = "i-closed"
    /\ progressState' = "i-closed"

Next == ProgressAction \/ OtherAction

Spec ==
    /\ Init
    /\ [][Next]_progressVars
    /\ WF_progressVars(ProgressAction)

ImplementationType == progressState \in ImplementationStates
ImplementationSafe ==
    progressState \in ConcreteSafeStates(
        ImplementationStates, FormalSafeStates, Abstraction)
ImplementationObservationAllowed ==
    ImplementationObserve[progressState] \in AllowedObservations
EventualImplementationClosure ==
    <> (progressState \in ImplementationClosedStates)

====
