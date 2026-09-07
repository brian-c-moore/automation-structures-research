---- MODULE CommonSemanticSchema_Proof ----
EXTENDS CommonSemanticSchema, TLAPS

CONSTANTS S, InitialStates, InvariantStates,
          StepA, StepB, SharedSteps, EnvironmentSteps, RelyA, RelyB,
          ImplementationStates, FormalStates,
          ImplementationInitial, FormalInitial,
          ImplementationSteps, FormalSteps,
          ObservationDomain,
          Abstraction, ImplementationObserve, FormalObserve,
          FormalSafeStates

THEOREM MutualClosureComposition ==
    AdmittedMutualComposition(
        S, InitialStates, InvariantStates,
        StepA, StepB, SharedSteps, EnvironmentSteps, RelyA, RelyB)
    => Stable(S, InvariantStates,
              StepA \cup StepB \cup SharedSteps \cup EnvironmentSteps)
BY SMT DEF AdmittedMutualComposition, MutualSafetyClosure, Stable

THEOREM FunctionalConformanceSafetyTransfer ==
    /\ FunctionalConformance(
           ImplementationStates, FormalStates,
           ImplementationInitial, FormalInitial,
           ImplementationSteps, FormalSteps,
           ObservationDomain, Abstraction,
           ImplementationObserve, FormalObserve)
    /\ FormalSafeStates \subseteq FormalStates
    /\ Initializes(FormalInitial, FormalSafeStates)
    /\ Stable(FormalStates, FormalSafeStates, FormalSteps)
    => /\ Initializes(
              ImplementationInitial,
              ConcreteSafeStates(
                  ImplementationStates, FormalSafeStates, Abstraction))
       /\ Stable(
              ImplementationStates,
              ConcreteSafeStates(
                  ImplementationStates, FormalSafeStates, Abstraction),
              ImplementationSteps)
PROOF
  <1> SUFFICES ASSUME
        FunctionalConformance(
            ImplementationStates, FormalStates,
            ImplementationInitial, FormalInitial,
            ImplementationSteps, FormalSteps,
            ObservationDomain, Abstraction,
            ImplementationObserve, FormalObserve),
        FormalSafeStates \subseteq FormalStates,
        Initializes(FormalInitial, FormalSafeStates),
        Stable(FormalStates, FormalSafeStates, FormalSteps)
      PROVE
        /\ Initializes(
               ImplementationInitial,
               ConcreteSafeStates(
                   ImplementationStates, FormalSafeStates, Abstraction))
        /\ Stable(
               ImplementationStates,
               ConcreteSafeStates(
                   ImplementationStates, FormalSafeStates, Abstraction),
               ImplementationSteps)
    OBVIOUS
  <1>init. Initializes(
        ImplementationInitial,
        ConcreteSafeStates(
            ImplementationStates, FormalSafeStates, Abstraction))
    BY SMT DEF FunctionalConformance, InitialStatesRefine,
               Initializes, ConcreteSafeStates
  <1>step. Stable(
        ImplementationStates,
        ConcreteSafeStates(
            ImplementationStates, FormalSafeStates, Abstraction),
        ImplementationSteps)
    <2> SUFFICES ASSUME
          NEW i \in ConcreteSafeStates(
              ImplementationStates, FormalSafeStates, Abstraction),
          NEW j \in ImplementationStates,
          <<i, j>> \in ImplementationSteps
        PROVE j \in ConcreteSafeStates(
              ImplementationStates, FormalSafeStates, Abstraction)
      BY DEF Stable
    <2>i. /\ i \in ImplementationStates
            /\ Abstraction[i] \in FormalSafeStates
      BY DEF ConcreteSafeStates
    <2>map. <<Abstraction[i], Abstraction[j]>>
          \in FormalSteps \cup IdentityRelation(FormalStates)
      BY DEF FunctionalConformance, StepsRefine, MappedPair
    <2>af. Abstraction \in [ImplementationStates -> FormalStates]
      BY DEF FunctionalConformance
    <2>aj. Abstraction[j] \in FormalStates
      BY <2>af
    <2>formal. CASE <<Abstraction[i], Abstraction[j]>> \in FormalSteps
      <3>1. Abstraction[j] \in FormalSafeStates
        BY <2>i, <2>aj, <2>formal DEF Stable
      <3> QED BY <3>1 DEF ConcreteSafeStates
    <2>stutter. CASE
          <<Abstraction[i], Abstraction[j]>> \in IdentityRelation(FormalStates)
      <3>1. Abstraction[j] = Abstraction[i]
        BY <2>stutter DEF IdentityRelation
      <3>2. Abstraction[j] \in FormalSafeStates
        BY <2>i, <3>1
      <3> QED BY <3>2 DEF ConcreteSafeStates
    <2> QED BY <2>map, <2>formal, <2>stutter
  <1> QED BY <1>init, <1>step

====
