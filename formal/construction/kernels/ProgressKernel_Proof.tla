---- MODULE ProgressKernel_Proof ----
EXTENDS ProgressKernel, NaturalsInduction, TLAPS

CONSTANTS ProgressStates, ProgressActiveStates, ProgressClosedStates,
          DecreasingSteps, NonprogressSteps,
          ProgressRankBound, ProgressRank,
          ProgressFairnessOwners, ProgressFairnessOwner,
          ProgressFairnessOwnerOf

Premises ==
    RankedProgressPremises(
        ProgressStates, ProgressActiveStates, ProgressClosedStates,
        DecreasingSteps, NonprogressSteps,
        ProgressRankBound, ProgressRank,
        ProgressFairnessOwners, ProgressFairnessOwner,
        ProgressFairnessOwnerOf)

Spec ==
    RankedProgressSpec(
        ProgressStates, DecreasingSteps, NonprogressSteps)

LEMMA RankedProgressInitType ==
    Premises /\ RankedProgressInit(ProgressStates)
      => RankedProgressType(ProgressStates)
BY DEF Premises, RankedProgressInit, RankedProgressType

LEMMA RankedProgressNextType ==
    Premises /\ RankedProgressType(ProgressStates)
        /\ [RankedProgressNext(DecreasingSteps, NonprogressSteps)]_progressVars
    => RankedProgressType(ProgressStates)'
BY SMT DEF Premises, RankedProgressPremises,
           RankedProgressType, RankedProgressNext,
           RankedProgressAction, RankedOtherAction,
           RelationTyped, Pairs, FairnessOwnershipTyped,
           ProgressMeasureTyped, progressVars

THEOREM RankedProgressTypeSafety ==
    Premises /\ Spec => []RankedProgressType(ProgressStates)
PROOF
  <1> SUFFICES ASSUME Premises
               PROVE Spec => []RankedProgressType(ProgressStates)
    OBVIOUS
  <1>init. RankedProgressInit(ProgressStates)
          => RankedProgressType(ProgressStates)
    BY DEF RankedProgressInit, RankedProgressType
  <1>next. RankedProgressType(ProgressStates)
          /\ [RankedProgressNext(
                 DecreasingSteps, NonprogressSteps)]_progressVars
        => RankedProgressType(ProgressStates)'
    BY RankedProgressNextType
  <1> QED BY <1>init, <1>next, PTL DEF Spec, RankedProgressSpec

THEOREM RankedProgress ==
    Premises /\ Spec => EventualRankedClosure(ProgressClosedStates)
PROOF
  <1> SUFFICES ASSUME Premises
               PROVE Spec => EventualRankedClosure(ProgressClosedStates)
    OBVIOUS
  <1> DEFINE P(m) ==
        Spec => <>RankedLevel(ProgressClosedStates, ProgressRank, m)
  <1> HIDE DEF P
  <1>base. P(ProgressRankBound)
    <2> SUFFICES ASSUME Spec
          PROVE <>RankedLevel(
              ProgressClosedStates, ProgressRank, ProgressRankBound)
      BY DEF P
    <2>1. RankedProgressInit(ProgressStates)
              => RankedLevel(
                   ProgressClosedStates, ProgressRank, ProgressRankBound)
      BY SMT DEF Premises, RankedProgressPremises,
                 ProgressMeasureTyped, RankedProgressInit, RankedLevel
    <2> QED BY <2>1, PTL DEF Spec, RankedProgressSpec
  <1>step. \A n \in 1..ProgressRankBound : P(n) => P(n - 1)
    <2> SUFFICES ASSUME NEW n \in 1..ProgressRankBound
          PROVE Spec
            /\ <>RankedLevel(ProgressClosedStates, ProgressRank, n)
              => <>RankedLevel(
                   ProgressClosedStates, ProgressRank, n - 1)
      BY DEF P
    <2>i. RankedProgressType(ProgressStates)
              /\ RankedLevel(ProgressClosedStates, ProgressRank, n)
              /\ [RankedProgressNext(
                     DecreasingSteps, NonprogressSteps)]_progressVars
            => \/ RankedLevel(
                       ProgressClosedStates, ProgressRank, n)'
               \/ RankedLevel(
                       ProgressClosedStates, ProgressRank, n - 1)'
      <3> SUFFICES ASSUME
            RankedProgressType(ProgressStates),
            RankedLevel(ProgressClosedStates, ProgressRank, n),
            [RankedProgressNext(
                DecreasingSteps, NonprogressSteps)]_progressVars
          PROVE
            \/ RankedLevel(ProgressClosedStates, ProgressRank, n)'
            \/ RankedLevel(ProgressClosedStates, ProgressRank, n - 1)'
        OBVIOUS
      <3>0. CASE UNCHANGED progressVars
        BY <3>0 DEF RankedLevel, progressVars
      <3>P. CASE RankedProgressAction(DecreasingSteps)
        BY <3>P, SMT DEF Premises, RankedProgressPremises,
                          ProgressMeasureTyped, RankedProgressType,
                          RankedProgressAction, RankedLevel,
                          RelationTyped, Pairs, FairnessOwnershipTyped
      <3>O. CASE RankedOtherAction(NonprogressSteps)
        BY <3>O, SMT DEF Premises, RankedProgressPremises,
                          ProgressMeasureTyped, RankedProgressType,
                          RankedOtherAction, RankedLevel,
                          RelationTyped, Pairs, FairnessOwnershipTyped
      <3>N. CASE RankedProgressNext(
                       DecreasingSteps, NonprogressSteps)
        BY <3>N, <3>P, <3>O DEF RankedProgressNext
      <3> QED BY <3>0, <3>N
    <2>ii. RankedProgressType(ProgressStates)
               /\ RankedLevel(ProgressClosedStates, ProgressRank, n)
               /\ <<RankedProgressNext(
                         DecreasingSteps, NonprogressSteps)
                      /\ RankedProgressAction(DecreasingSteps)>>_progressVars
             => RankedLevel(
                    ProgressClosedStates, ProgressRank, n - 1)'
      BY SMT DEF Premises, RankedProgressPremises,
                 ProgressMeasureTyped, RankedProgressType,
                 RankedProgressNext, RankedProgressAction,
                 RankedOtherAction, RankedLevel, progressVars,
                 RelationTyped, Pairs, FairnessOwnershipTyped
    <2>iii. RankedProgressType(ProgressStates)
                /\ RankedLevel(ProgressClosedStates, ProgressRank, n)
                /\ ~RankedLevel(
                        ProgressClosedStates, ProgressRank, n - 1)
              => ENABLED
                   <<RankedProgressAction(DecreasingSteps)>>_progressVars
      <3> SUFFICES ASSUME
            RankedProgressType(ProgressStates),
            RankedLevel(ProgressClosedStates, ProgressRank, n),
            ~RankedLevel(ProgressClosedStates, ProgressRank, n - 1)
          PROVE ENABLED
            <<RankedProgressAction(DecreasingSteps)>>_progressVars
        OBVIOUS
      <3>active. progressState \in ProgressActiveStates
        BY SMT DEF Premises, RankedProgressPremises,
                   ProgressMeasureTyped, RankedProgressType, RankedLevel
      <3>step. \E t \in ProgressStates :
          <<progressState, t>> \in DecreasingSteps
        BY <3>active DEF Premises, RankedProgressPremises
      <3>decreases. \A t \in ProgressStates :
          <<progressState, t>> \in DecreasingSteps
            => ProgressRank[t] < ProgressRank[progressState]
        BY DEF Premises, RankedProgressPremises
      <3>different. \A t \in ProgressStates :
          <<progressState, t>> \in DecreasingSteps
            => t # progressState
        <4> SUFFICES ASSUME
              NEW t \in ProgressStates,
              <<progressState, t>> \in DecreasingSteps
            PROVE t # progressState
          OBVIOUS
        <4>less. ProgressRank[t] < ProgressRank[progressState]
          BY <3>decreases
        <4>ranks. /\ ProgressRank[t] \in Nat
                   /\ ProgressRank[progressState] \in Nat
          BY SMT DEF Premises, RankedProgressPremises,
                     ProgressMeasureTyped, RankedProgressType
        <4> QED BY <4>less, <4>ranks, SMT
      <3> QED BY <3>step, <3>different, ExpandENABLED, SMT
           DEF RankedProgressAction, progressVars
    <2>wf. Spec
          => WF_progressVars(RankedProgressAction(DecreasingSteps))
      BY DEF Spec, RankedProgressSpec, RankedProgressFairness
    <2> QED BY <2>i, <2>ii, <2>iii, <2>wf,
                 RankedProgressTypeSafety, PTL
             DEF Spec, RankedProgressSpec
  <1>down. P(0)
    BY <1>base, <1>step, DownwardNatInduction
       DEF Premises, RankedProgressPremises, ProgressMeasureTyped
  <1>zero. RankedProgressType(ProgressStates)
               /\ RankedLevel(ProgressClosedStates, ProgressRank, 0)
             => RankedClosure(ProgressClosedStates)
    BY SMT DEF Premises, RankedProgressPremises,
               ProgressMeasureTyped, RankedProgressType,
               RankedLevel, RankedClosure
  <1>types. Spec => []RankedProgressType(ProgressStates)
    BY RankedProgressTypeSafety
  <1> QED BY <1>down, <1>zero, <1>types, PTL
       DEF P, EventualRankedClosure

====
