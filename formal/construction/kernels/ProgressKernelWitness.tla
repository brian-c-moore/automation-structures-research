---- MODULE ProgressKernelWitness ----
EXTENDS TheoryKernel

VARIABLE state

vars == <<state>>

ProgressTheory == INSTANCE ProgressKernel WITH progressState <- state

States == {"two", "one", "closed"}
ActiveStates == {"two", "one"}
ClosedStates == {"closed"}

Rank ==
    [s \in States |->
        CASE s = "two" -> 2
          [] s = "one" -> 1
          [] OTHER -> 0]
RankBound == 2

ProgressSteps == {<<"two", "one">>, <<"one", "closed">>}
OtherSteps == IdentityRelation(States)

FairnessOwners == {"deployment-scheduler"}
FairnessOwner == "deployment-scheduler"
FairnessOwnerOf == [step \in ProgressSteps |-> FairnessOwner]
WrongFairnessOwners ==
    {"deployment-scheduler", "unrelated-actor"}
WrongFairnessOwnerOf ==
    [step \in ProgressSteps |-> "unrelated-actor"]

RejectsMisattributedFairness ==
    ~ProgressTheory!FairnessOwnershipTyped(
        WrongFairnessOwners, FairnessOwner,
        ProgressSteps, WrongFairnessOwnerOf)

EmptyProgressSteps == {}
EmptyFairnessOwnerOf ==
    [step \in EmptyProgressSteps |-> FairnessOwner]

RejectsEmptyProgress ==
    ~ProgressTheory!RankedProgressPremises(
        States, ActiveStates, ClosedStates,
        EmptyProgressSteps, OtherSteps, RankBound, Rank,
        FairnessOwners, FairnessOwner, EmptyFairnessOwnerOf)

OverlappingOtherSteps == OtherSteps \cup ProgressSteps

RejectsOverlappingProgressClasses ==
    ~ProgressTheory!RankedProgressPremises(
        States, ActiveStates, ClosedStates,
        ProgressSteps, OverlappingOtherSteps, RankBound, Rank,
        FairnessOwners, FairnessOwner, FairnessOwnerOf)

StructuralPremises ==
    ProgressTheory!RankedProgressPremises(
        States, ActiveStates, ClosedStates,
        ProgressSteps, OtherSteps, RankBound, Rank,
        FairnessOwners, FairnessOwner, FairnessOwnerOf)

Init == state = "two"

ProgressAction ==
    \/ /\ state = "two"
       /\ state' = "one"
    \/ /\ state = "one"
       /\ state' = "closed"

OtherAction == UNCHANGED vars

Next == ProgressAction \/ OtherAction

Fairness == WF_vars(ProgressAction)

Spec == Init /\ [][Next]_vars /\ Fairness

EventualClosure == <>(state \in ClosedStates)

====
