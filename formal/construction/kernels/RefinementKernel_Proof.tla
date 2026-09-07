---- MODULE RefinementKernel_Proof ----
EXTENDS RefinementKernel, ProgressKernel_Proof, TLAPS

CONSTANTS SelectedClasses,
          FormalStates,
          ImplementationInitial, FormalInitial,
          ImplementationSteps, FormalSteps, FormalSafeStates,
          FormalObservationStates, ObservationDomain, AllowedObservations,
          Abstraction, ImplementationObserve, FormalObserve,
          FormalClosedStates, FormalProgressSteps, FormalOtherSteps,
          FormalRank, FormalFairnessOwnerOf

THEOREM SafetyRefinementTransfer ==
    SafetyRefinementPremises(
        ProgressStates, FormalStates,
        ImplementationInitial, FormalInitial,
        ImplementationSteps, FormalSteps,
        FormalSafeStates, ObservationDomain,
        Abstraction, ImplementationObserve, FormalObserve)
    => SafetyRefinementConclusion(
           ProgressStates, ImplementationInitial,
           ImplementationSteps, FormalSafeStates, Abstraction)
PROOF
  <1> SUFFICES ASSUME
        SafetyRefinementPremises(
            ProgressStates, FormalStates,
            ImplementationInitial, FormalInitial,
            ImplementationSteps, FormalSteps,
            FormalSafeStates, ObservationDomain,
            Abstraction, ImplementationObserve, FormalObserve)
      PROVE
        SafetyRefinementConclusion(
            ProgressStates, ImplementationInitial,
            ImplementationSteps, FormalSafeStates, Abstraction)
    OBVIOUS
  <1>init. Initializes(
        ImplementationInitial,
        ConcreteSafeStates(
            ProgressStates, FormalSafeStates, Abstraction))
    BY SMT DEF SafetyRefinementPremises, FunctionalConformance,
               InitialStatesRefine, Initializes, ConcreteSafeStates
  <1>step. Stable(
        ProgressStates,
        ConcreteSafeStates(
            ProgressStates, FormalSafeStates, Abstraction),
        ImplementationSteps)
    <2> SUFFICES ASSUME
          NEW i \in ConcreteSafeStates(
              ProgressStates, FormalSafeStates, Abstraction),
          NEW j \in ProgressStates,
          <<i, j>> \in ImplementationSteps
        PROVE j \in ConcreteSafeStates(
              ProgressStates, FormalSafeStates, Abstraction)
      BY DEF Stable
    <2>map. <<Abstraction[i], Abstraction[j]>>
          \in FormalSteps \cup IdentityRelation(FormalStates)
      BY DEF SafetyRefinementPremises, FunctionalConformance,
             StepsRefine, MappedPair
    <2>i. /\ i \in ProgressStates
            /\ Abstraction[i] \in FormalSafeStates
      BY DEF ConcreteSafeStates
    <2>af. Abstraction \in [ProgressStates -> FormalStates]
      BY DEF SafetyRefinementPremises, FunctionalConformance
    <2>j. Abstraction[j] \in FormalStates
      BY <2>af
    <2>formal. CASE <<Abstraction[i], Abstraction[j]>> \in FormalSteps
      <3>1. Abstraction[j] \in FormalSafeStates
        BY <2>i, <2>j, <2>formal
           DEF SafetyRefinementPremises, Stable
      <3> QED BY <3>1 DEF ConcreteSafeStates
    <2>stutter. CASE
          <<Abstraction[i], Abstraction[j]>> \in IdentityRelation(FormalStates)
      <3>1. Abstraction[j] = Abstraction[i]
        BY <2>stutter DEF IdentityRelation
      <3> QED BY <2>i, <3>1 DEF ConcreteSafeStates
    <2> QED BY <2>map, <2>formal, <2>stutter
  <1> QED BY <1>init, <1>step DEF SafetyRefinementConclusion

THEOREM ObservationPropertyTransfer ==
    ObservationPropertyPremises(
        ProgressStates, FormalStates,
        FormalObservationStates, ObservationDomain,
        AllowedObservations, Abstraction,
        ImplementationObserve, FormalObserve)
    => ObservationPropertyConclusion(
           ProgressStates, FormalObservationStates,
           AllowedObservations, Abstraction,
           ImplementationObserve)
BY SMT DEF ObservationPropertyPremises,
           ObservationPropertyConclusion, ObservationsAgree,
           ConcreteSafeStates

THEOREM LivenessPremisesLift ==
    LivenessRefinementPremises(
        ProgressStates, ProgressActiveStates, ProgressClosedStates,
        FormalStates,
        FormalClosedStates, FormalProgressSteps, FormalOtherSteps,
        ImplementationSteps, DecreasingSteps, NonprogressSteps,
        ProgressRankBound, FormalRank, ProgressRank, Abstraction,
        ProgressFairnessOwners, ProgressFairnessOwner,
        FormalFairnessOwnerOf, ProgressFairnessOwnerOf)
    => ConcreteRankedProgressPremises(
           ProgressStates, ProgressActiveStates, ProgressClosedStates,
           DecreasingSteps, NonprogressSteps,
           ProgressRankBound, ProgressRank,
           ProgressFairnessOwners, ProgressFairnessOwner,
           ProgressFairnessOwnerOf)
PROOF
  <1> SUFFICES ASSUME
        LivenessRefinementPremises(
            ProgressStates, ProgressActiveStates, ProgressClosedStates,
            FormalStates,
            FormalClosedStates, FormalProgressSteps, FormalOtherSteps,
            ImplementationSteps, DecreasingSteps, NonprogressSteps,
            ProgressRankBound, FormalRank, ProgressRank, Abstraction,
            ProgressFairnessOwners, ProgressFairnessOwner,
            FormalFairnessOwnerOf, ProgressFairnessOwnerOf)
      PROVE
        ConcreteRankedProgressPremises(
            ProgressStates, ProgressActiveStates, ProgressClosedStates,
            DecreasingSteps, NonprogressSteps,
            ProgressRankBound, ProgressRank,
            ProgressFairnessOwners, ProgressFairnessOwner,
            ProgressFairnessOwnerOf)
    OBVIOUS
  <1> DEFINE IClosed ==
        ConcreteClosedStates(
            ProgressStates, FormalClosedStates, Abstraction)
  <1>measure. ProgressMeasureTyped(
        ProgressStates, IClosed, ProgressRankBound, ProgressRank)
    BY SMT DEF LivenessRefinementPremises, RankedProgressPremises,
               ProgressMeasureTyped, ConcreteClosedStates,
               ConcreteSafeStates, LiftedRank, IClosed
  <1>active. ProgressActiveStates = ProgressStates \ IClosed
    BY DEF LivenessRefinementPremises, IClosed
  <1>active_inhabited. ProgressActiveStates # {}
    BY DEF LivenessRefinementPremises
  <1>closed. ProgressClosedStates = IClosed
    BY DEF LivenessRefinementPremises, IClosed
  <1>progress_type. RelationTyped(ProgressStates, DecreasingSteps)
    BY DEF LivenessRefinementPremises
  <1>progress_inhabited. DecreasingSteps # {}
    BY DEF LivenessRefinementPremises
  <1>other_type. RelationTyped(ProgressStates, NonprogressSteps)
    BY DEF LivenessRefinementPremises
  <1>disjoint. DecreasingSteps \cap NonprogressSteps = {}
    BY DEF LivenessRefinementPremises
  <1>owner. FairnessOwnershipTyped(
        ProgressFairnessOwners, ProgressFairnessOwner,
        DecreasingSteps, ProgressFairnessOwnerOf)
    BY DEF LivenessRefinementPremises, RankedProgressPremises
  <1>decrease. \A pair \in DecreasingSteps :
        /\ pair[1] \in ProgressActiveStates
        /\ ProgressRank[pair[2]] < ProgressRank[pair[1]]
    <2> SUFFICES ASSUME NEW pair \in DecreasingSteps
          PROVE /\ pair[1] \in ProgressActiveStates
                /\ ProgressRank[pair[2]] < ProgressRank[pair[1]]
      OBVIOUS
    <2>typed. /\ pair[1] \in ProgressStates
                /\ pair[2] \in ProgressStates
      BY SMT DEF LivenessRefinementPremises, RelationTyped, Pairs
    <2>map. <<Abstraction[pair[1]], Abstraction[pair[2]]>>
          \in FormalProgressSteps
      BY DEF LivenessRefinementPremises,
             StepsRefineWithoutStutter, MappedPair
    <2>formal. /\ Abstraction[pair[1]]
                       \in FormalStates \ FormalClosedStates
                 /\ FormalRank[Abstraction[pair[2]]]
                       < FormalRank[Abstraction[pair[1]]]
      BY <2>map DEF LivenessRefinementPremises, RankedProgressPremises
    <2>source. pair[1] \in ProgressActiveStates
      BY <1>active, <2>typed, <2>formal
         DEF IClosed, ConcreteClosedStates, ConcreteSafeStates
    <2>rank. ProgressRank[pair[2]] < ProgressRank[pair[1]]
      BY <2>typed, <2>formal
         DEF LivenessRefinementPremises, LiftedRank
    <2> QED BY <2>source, <2>rank
  <1>nonincrease. \A pair \in NonprogressSteps :
        ProgressRank[pair[2]] <= ProgressRank[pair[1]]
    <2> SUFFICES ASSUME NEW pair \in NonprogressSteps
          PROVE ProgressRank[pair[2]] <= ProgressRank[pair[1]]
      OBVIOUS
    <2>typed. /\ pair[1] \in ProgressStates
                /\ pair[2] \in ProgressStates
      BY SMT DEF LivenessRefinementPremises, RelationTyped, Pairs
    <2>map. <<Abstraction[pair[1]], Abstraction[pair[2]]>>
          \in FormalOtherSteps \cup IdentityRelation(FormalStates)
      BY DEF LivenessRefinementPremises, StepsRefine, MappedPair
    <2>left. ProgressRank[pair[2]] =
          FormalRank[Abstraction[pair[2]]]
      BY <2>typed DEF LivenessRefinementPremises, LiftedRank
    <2>right. ProgressRank[pair[1]] =
          FormalRank[Abstraction[pair[1]]]
      BY <2>typed DEF LivenessRefinementPremises, LiftedRank
    <2>ranks. /\ FormalRank[Abstraction[pair[1]]] \in Nat
                /\ FormalRank[Abstraction[pair[2]]] \in Nat
      BY <2>typed DEF LivenessRefinementPremises,
                         RankedProgressPremises, ProgressMeasureTyped
    <2>formal. CASE
          <<Abstraction[pair[1]], Abstraction[pair[2]]>>
            \in FormalOtherSteps
      <3>1. FormalRank[Abstraction[pair[2]]]
              <= FormalRank[Abstraction[pair[1]]]
        BY <2>formal DEF LivenessRefinementPremises,
                          RankedProgressPremises
      <3> QED BY <2>left, <2>right, <2>ranks, <3>1, SMT
    <2>stutter. CASE
          <<Abstraction[pair[1]], Abstraction[pair[2]]>>
            \in IdentityRelation(FormalStates)
      <3>1. Abstraction[pair[2]] = Abstraction[pair[1]]
        BY <2>stutter DEF IdentityRelation
      <3> QED BY <2>left, <2>right, <2>ranks, <3>1, SMT
    <2> QED BY <2>map, <2>formal, <2>stutter
  <1>successor. \A i \in ProgressActiveStates :
        \E j \in ProgressStates : <<i, j>> \in DecreasingSteps
    BY <1>active DEF LivenessRefinementPremises, IClosed
  <1> QED
    BY <1>measure, <1>active, <1>active_inhabited, <1>closed,
       <1>progress_type, <1>progress_inhabited, <1>other_type,
       <1>disjoint, <1>owner, <1>decrease, <1>nonincrease, <1>successor
       DEF ConcreteRankedProgressPremises, RankedProgressPremises,
           IClosed

THEOREM LivenessRefinementTransfer ==
    /\ LivenessRefinementPremises(
           ProgressStates, ProgressActiveStates, ProgressClosedStates,
           FormalStates,
           FormalClosedStates, FormalProgressSteps, FormalOtherSteps,
           ImplementationSteps, DecreasingSteps, NonprogressSteps,
           ProgressRankBound, FormalRank, ProgressRank, Abstraction,
           ProgressFairnessOwners, ProgressFairnessOwner,
           FormalFairnessOwnerOf, ProgressFairnessOwnerOf)
    /\ RankedProgressSpec(
           ProgressStates, DecreasingSteps, NonprogressSteps)
    => EventualRankedClosure(ProgressClosedStates)
PROOF
  <1> SUFFICES ASSUME
        LivenessRefinementPremises(
            ProgressStates, ProgressActiveStates, ProgressClosedStates,
            FormalStates,
            FormalClosedStates, FormalProgressSteps, FormalOtherSteps,
            ImplementationSteps, DecreasingSteps, NonprogressSteps,
            ProgressRankBound, FormalRank, ProgressRank, Abstraction,
            ProgressFairnessOwners, ProgressFairnessOwner,
            FormalFairnessOwnerOf, ProgressFairnessOwnerOf),
        RankedProgressSpec(
            ProgressStates, DecreasingSteps, NonprogressSteps)
      PROVE EventualRankedClosure(ProgressClosedStates)
    OBVIOUS
  <1>premises. Premises
    BY LivenessPremisesLift
       DEF Premises, ConcreteRankedProgressPremises
  <1>spec. Spec
    BY DEF Spec
  <1> QED BY <1>premises, <1>spec, RankedProgress

THEOREM ClassSpecificRefinementTransfer ==
    RefinementTransferPremises(
        SelectedClasses,
        ProgressStates, ProgressActiveStates, ProgressClosedStates,
        FormalStates,
        ImplementationInitial, FormalInitial,
        ImplementationSteps, FormalSteps, FormalSafeStates,
        FormalObservationStates, ObservationDomain, AllowedObservations,
        Abstraction, ImplementationObserve, FormalObserve,
        FormalClosedStates, FormalProgressSteps, FormalOtherSteps,
        DecreasingSteps, NonprogressSteps,
        ProgressRankBound, FormalRank, ProgressRank,
        ProgressFairnessOwners, ProgressFairnessOwner,
        FormalFairnessOwnerOf, ProgressFairnessOwnerOf)
    => RefinementTransferConclusion(
           SelectedClasses,
           ProgressStates, ProgressClosedStates,
           ImplementationInitial,
           ImplementationSteps, FormalSafeStates,
           FormalObservationStates, AllowedObservations,
           Abstraction, ImplementationObserve)
BY SafetyRefinementTransfer, ObservationPropertyTransfer,
   LivenessRefinementTransfer
   DEF RefinementTransferPremises, RefinementTransferConclusion

====
