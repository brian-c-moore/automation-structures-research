---- MODULE RefinementKernel ----
EXTENDS ProgressKernel

RefinementClasses == {"safety", "liveness", "observation"}

SafetyRefinementPremises(
        ImplementationStates, FormalStates,
        ImplementationInitial, FormalInitial,
        ImplementationSteps, FormalSteps,
        FormalSafeStates, ObservationDomain,
        Abstraction, ImplementationObserve, FormalObserve) ==
    /\ FunctionalConformance(
           ImplementationStates, FormalStates,
           ImplementationInitial, FormalInitial,
           ImplementationSteps, FormalSteps,
           ObservationDomain, Abstraction,
           ImplementationObserve, FormalObserve)
    /\ FormalSafeStates \subseteq FormalStates
    /\ Initializes(FormalInitial, FormalSafeStates)
    /\ Stable(FormalStates, FormalSafeStates, FormalSteps)

SafetyRefinementConclusion(
        ImplementationStates, ImplementationInitial,
        ImplementationSteps, FormalSafeStates, Abstraction) ==
    /\ Initializes(
           ImplementationInitial,
           ConcreteSafeStates(
               ImplementationStates, FormalSafeStates, Abstraction))
    /\ Stable(
           ImplementationStates,
           ConcreteSafeStates(
               ImplementationStates, FormalSafeStates, Abstraction),
           ImplementationSteps)

ObservationPropertyPremises(
        ImplementationStates, FormalStates,
        FormalObservationStates, ObservationDomain,
        AllowedObservations, Abstraction,
        ImplementationObserve, FormalObserve) ==
    /\ FormalObservationStates \subseteq FormalStates
    /\ AllowedObservations \subseteq ObservationDomain
    /\ Abstraction \in [ImplementationStates -> FormalStates]
    /\ ImplementationObserve
         \in [ImplementationStates -> ObservationDomain]
    /\ FormalObserve \in [FormalStates -> ObservationDomain]
    /\ ObservationsAgree(
           ImplementationStates, ImplementationObserve,
           FormalObserve, Abstraction)
    /\ \A f \in FormalObservationStates :
          FormalObserve[f] \in AllowedObservations

ObservationPropertyConclusion(
        ImplementationStates, FormalObservationStates,
        AllowedObservations, Abstraction,
        ImplementationObserve) ==
    \A i \in ConcreteSafeStates(
                    ImplementationStates,
                    FormalObservationStates, Abstraction) :
        ImplementationObserve[i] \in AllowedObservations

ConcreteClosedStates(
        ImplementationStates, FormalClosedStates, Abstraction) ==
    ConcreteSafeStates(
        ImplementationStates, FormalClosedStates, Abstraction)

LiftedRank(ImplementationStates, Abstraction, FormalRank) ==
    [i \in ImplementationStates |-> FormalRank[Abstraction[i]]]

LivenessRefinementPremises(
        ImplementationStates, ImplementationActiveStates,
        ImplementationClosedStates, FormalStates,
        FormalClosedStates, FormalProgressSteps, FormalOtherSteps,
        ImplementationSteps, ImplementationProgressSteps,
        ImplementationOtherSteps,
        RankBound, FormalRank, ImplementationRank, Abstraction,
        FairnessOwners, FairnessOwner,
        FormalFairnessOwnerOf, ImplementationFairnessOwnerOf) ==
    LET ConcreteClosed ==
          ConcreteClosedStates(
              ImplementationStates, FormalClosedStates, Abstraction)
    IN
    /\ RankedProgressPremises(
           FormalStates, FormalStates \ FormalClosedStates,
           FormalClosedStates, FormalProgressSteps, FormalOtherSteps,
           RankBound, FormalRank, FairnessOwners, FairnessOwner,
           FormalFairnessOwnerOf)
    /\ Abstraction \in [ImplementationStates -> FormalStates]
    /\ ImplementationActiveStates =
         ImplementationStates \ ConcreteClosed
    /\ ImplementationActiveStates # {}
    /\ ImplementationClosedStates = ConcreteClosed
    /\ ImplementationRank =
         LiftedRank(ImplementationStates, Abstraction, FormalRank)
    /\ RelationTyped(
           ImplementationStates, ImplementationProgressSteps)
    /\ ImplementationProgressSteps # {}
    /\ RelationTyped(ImplementationStates, ImplementationOtherSteps)
    /\ ImplementationSteps =
         ImplementationProgressSteps \cup ImplementationOtherSteps
    /\ ImplementationProgressSteps \cap ImplementationOtherSteps = {}
    /\ FairnessOwnershipTyped(
           FairnessOwners, FairnessOwner,
           ImplementationProgressSteps,
           ImplementationFairnessOwnerOf)
    /\ StepsRefineWithoutStutter(
           ImplementationProgressSteps,
           FormalProgressSteps, Abstraction)
    /\ StepsRefine(
           ImplementationOtherSteps, FormalStates,
           FormalOtherSteps, Abstraction)
    /\ \A i \in ImplementationStates \ ConcreteClosed :
          \E j \in ImplementationStates :
              <<i, j>> \in ImplementationProgressSteps

ConcreteRankedProgressPremises(
        ImplementationStates, ImplementationActiveStates,
        ImplementationClosedStates,
        ImplementationProgressSteps, ImplementationOtherSteps,
        RankBound, ImplementationRank,
        FairnessOwners, FairnessOwner,
        ImplementationFairnessOwnerOf) ==
    RankedProgressPremises(
        ImplementationStates,
        ImplementationActiveStates, ImplementationClosedStates,
        ImplementationProgressSteps, ImplementationOtherSteps,
        RankBound, ImplementationRank, FairnessOwners, FairnessOwner,
        ImplementationFairnessOwnerOf)

RefinementTransferPremises(
        SelectedClasses,
        ImplementationStates, ImplementationActiveStates,
        ImplementationClosedStates, FormalStates,
        ImplementationInitial, FormalInitial,
        ImplementationSteps, FormalSteps, FormalSafeStates,
        FormalObservationStates, ObservationDomain, AllowedObservations,
        Abstraction, ImplementationObserve, FormalObserve,
        FormalClosedStates, FormalProgressSteps, FormalOtherSteps,
        ImplementationProgressSteps, ImplementationOtherSteps,
        RankBound, FormalRank, ImplementationRank,
        FairnessOwners, FairnessOwner,
        FormalFairnessOwnerOf, ImplementationFairnessOwnerOf) ==
    /\ SelectedClasses # {}
    /\ SelectedClasses \subseteq RefinementClasses
    /\ ("safety" \in SelectedClasses
         => SafetyRefinementPremises(
                ImplementationStates, FormalStates,
                ImplementationInitial, FormalInitial,
                ImplementationSteps, FormalSteps,
                FormalSafeStates, ObservationDomain,
                Abstraction, ImplementationObserve, FormalObserve))
    /\ ("observation" \in SelectedClasses
         => ObservationPropertyPremises(
                ImplementationStates, FormalStates,
                FormalObservationStates, ObservationDomain,
                AllowedObservations, Abstraction,
                ImplementationObserve, FormalObserve))
    /\ ("liveness" \in SelectedClasses
         => /\ LivenessRefinementPremises(
                   ImplementationStates, ImplementationActiveStates,
                   ImplementationClosedStates, FormalStates,
                   FormalClosedStates,
                   FormalProgressSteps, FormalOtherSteps,
                   ImplementationSteps, ImplementationProgressSteps,
                   ImplementationOtherSteps,
                   RankBound, FormalRank, ImplementationRank, Abstraction,
                   FairnessOwners, FairnessOwner,
                   FormalFairnessOwnerOf,
                   ImplementationFairnessOwnerOf)
            /\ RankedProgressSpec(
                   ImplementationStates,
                   ImplementationProgressSteps,
                   ImplementationOtherSteps))

RefinementTransferConclusion(
        SelectedClasses,
        ImplementationStates, ImplementationClosedStates,
        ImplementationInitial,
        ImplementationSteps, FormalSafeStates,
        FormalObservationStates, AllowedObservations,
        Abstraction, ImplementationObserve) ==
    /\ ("safety" \in SelectedClasses
         => SafetyRefinementConclusion(
                ImplementationStates, ImplementationInitial,
                ImplementationSteps, FormalSafeStates, Abstraction))
    /\ ("observation" \in SelectedClasses
         => ObservationPropertyConclusion(
                ImplementationStates, FormalObservationStates,
                AllowedObservations, Abstraction,
                ImplementationObserve))
    /\ ("liveness" \in SelectedClasses
         => EventualRankedClosure(ImplementationClosedStates))

====
