---- MODULE ProgressKernel ----
EXTENDS TheoryKernel

VARIABLE progressState

progressVars == <<progressState>>

FairnessOwnershipTyped(
        FairnessOwners, FairnessOwner,
        ProgressSteps, FairnessOwnerOf) ==
    /\ FairnessOwner \in FairnessOwners
    /\ FairnessOwnerOf \in [ProgressSteps -> FairnessOwners]
    /\ \A step \in ProgressSteps :
          FairnessOwnerOf[step] = FairnessOwner

RankedProgressPremises(
        S, ActiveStates, ClosedStates,
        ProgressSteps, OtherSteps, RankBound, Rank,
        FairnessOwners, FairnessOwner, FairnessOwnerOf) ==
    /\ ProgressMeasureTyped(S, ClosedStates, RankBound, Rank)
    /\ ActiveStates = S \ ClosedStates
    /\ ActiveStates # {}
    /\ RelationTyped(S, ProgressSteps)
    /\ ProgressSteps # {}
    /\ RelationTyped(S, OtherSteps)
    /\ ProgressSteps \cap OtherSteps = {}
    /\ FairnessOwnershipTyped(
           FairnessOwners, FairnessOwner,
           ProgressSteps, FairnessOwnerOf)
    /\ \A pair \in ProgressSteps :
          /\ pair[1] \in ActiveStates
          /\ Rank[pair[2]] < Rank[pair[1]]
    /\ \A pair \in OtherSteps :
          Rank[pair[2]] <= Rank[pair[1]]
    /\ \A s \in ActiveStates :
          \E t \in S : <<s, t>> \in ProgressSteps

RankedProgressType(S) == progressState \in S

RankedProgressInit(S) == progressState \in S

RankedProgressAction(ProgressSteps) ==
    <<progressState, progressState'>> \in ProgressSteps

RankedOtherAction(OtherSteps) ==
    <<progressState, progressState'>> \in OtherSteps

RankedProgressNext(ProgressSteps, OtherSteps) ==
    RankedProgressAction(ProgressSteps) \/ RankedOtherAction(OtherSteps)

RankedProgressFairness(ProgressSteps) ==
    WF_progressVars(RankedProgressAction(ProgressSteps))

RankedProgressSpec(S, ProgressSteps, OtherSteps) ==
    /\ RankedProgressInit(S)
    /\ [][RankedProgressNext(ProgressSteps, OtherSteps)]_progressVars
    /\ RankedProgressFairness(ProgressSteps)

RankedLevel(ClosedStates, Rank, n) ==
    progressState \in ClosedStates \/ Rank[progressState] <= n

RankedClosure(ClosedStates) == progressState \in ClosedStates

EventualRankedClosure(ClosedStates) == <>RankedClosure(ClosedStates)

====
