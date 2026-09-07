---- MODULE CommitClassificationBypass_NEG ----
EXTENDS CommonSemanticSchema, TLC

FormalStates == {"open", "closed", "failed"}
ImplementationStates ==
    {"i-open", "i-ready", "i-closed-builder", "i-closed-bypass",
     "i-failed"}

FormalInitial == {"open"}
ImplementationInitial == {"i-open"}

FormalCommitSteps == {<<"open", "closed">>}
FormalFailureSteps == {<<"open", "failed">>}
FormalSteps == FormalCommitSteps \cup FormalFailureSteps

DeclaredImplementationCommit ==
    {<<"i-ready", "i-closed-builder">>}
BypassImplementationCommit ==
    {<<"i-open", "i-closed-bypass">>}
ImplementationFailure == {<<"i-open", "i-failed">>}

CommitTestImplementationSteps ==
    DeclaredImplementationCommit \cup BypassImplementationCommit
FailureTestImplementationSteps ==
    DeclaredImplementationCommit \cup ImplementationFailure

Abstraction ==
    [state \in ImplementationStates |->
        CASE state \in {"i-open", "i-ready"} -> "open"
          [] state \in {"i-closed-builder", "i-closed-bypass"} -> "closed"
          [] OTHER -> "failed"]

ObservationDomain == {"open-view", "closed-view", "failed-view"}
FormalObserve ==
    [state \in FormalStates |->
        CASE state = "open" -> "open-view"
          [] state = "closed" -> "closed-view"
          [] OTHER -> "failed-view"]
ImplementationObserve ==
    [state \in ImplementationStates |-> FormalObserve[Abstraction[state]]]

ImplementationCommitOwner ==
    [pair \in DeclaredImplementationCommit |-> "builder"]
FormalCommitOwner == [pair \in FormalCommitSteps |-> "builder"]
ImplementationCommitDelegate ==
    [pair \in DeclaredImplementationCommit |-> "builder"]
FormalCommitDelegate == [pair \in FormalCommitSteps |-> "builder"]
ImplementationCommitAssurance ==
    [pair \in DeclaredImplementationCommit |-> "at-commit"]
FormalCommitAssurance ==
    [pair \in FormalCommitSteps |-> "at-commit"]

FormalPersistentObserve ==
    [state \in FormalStates |-> state = "closed"]
ImplementationPersistentObserve ==
    [state \in ImplementationStates |->
        FormalPersistentObserve[Abstraction[state]]]

StateAndStepSurfaceHeld ==
    FunctionalConformance(
        ImplementationStates, FormalStates,
        ImplementationInitial, FormalInitial,
        CommitTestImplementationSteps, FormalSteps,
        ObservationDomain, Abstraction,
        ImplementationObserve, FormalObserve)

DeclaredCommitSurfaceHeld ==
    /\ StepsRefineWithoutStutter(
           DeclaredImplementationCommit, FormalCommitSteps, Abstraction)
    /\ CommitBoundaryConformance(
           DeclaredImplementationCommit, FormalCommitSteps,
           ImplementationCommitOwner, FormalCommitOwner,
           ImplementationCommitDelegate, FormalCommitDelegate,
           ImplementationCommitAssurance, FormalCommitAssurance,
           Abstraction)

BypassMapsToGovernedCommit ==
    \A pair \in BypassImplementationCommit :
        MappedPair(Abstraction, pair) \in FormalCommitSteps

RejectsUnclassifiedCommit ==
    ~CommitFailureConformance(
        ImplementationStates, FormalStates,
        CommitTestImplementationSteps, FormalSteps,
        DeclaredImplementationCommit, FormalCommitSteps,
        {}, {}, Abstraction)

RejectsUnclassifiedFailure ==
    ~CommitFailureConformance(
        ImplementationStates, FormalStates,
        FailureTestImplementationSteps, FormalSteps,
        DeclaredImplementationCommit, FormalCommitSteps,
        {}, FormalFailureSteps, Abstraction)

VARIABLE state

vars == <<state>>

Init == state = "i-open"

BypassCommit ==
    /\ state = "i-open"
    /\ state' = "i-closed-bypass"

Next == BypassCommit \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

AdvertisedCommitOwner == state # "i-closed-bypass"

====
