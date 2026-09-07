---- MODULE CompositionKernel ----
EXTENDS TheoryKernel

CompositionComponents == {"component-a", "component-b"}

PossibleRelyEdges ==
    {<<"component-a", "component-b">>,
     <<"component-b", "component-a">>}

JointInvariant(InvA, InvB) == InvA \cap InvB

ComposedSteps(StepA, StepB, SharedSteps,
              EnvironmentSteps, FailureSteps) ==
    StepA \cup StepB \cup SharedSteps
      \cup EnvironmentSteps \cup FailureSteps

AcyclicRelyGraph(RelyEdges) ==
    /\ RelyEdges \subseteq PossibleRelyEdges
    /\ ~( /\ <<"component-a", "component-b">> \in RelyEdges
           /\ <<"component-b", "component-a">> \in RelyEdges )

CyclicRelyGraph(RelyEdges) ==
    /\ RelyEdges = PossibleRelyEdges

CompositionBoundaryPremises(
        S, InitialStates, InvA, InvB,
        StepA, StepB, SharedSteps,
        EnvironmentSteps, FailureSteps, InterferenceSteps,
        RelyA, RelyB, Providers, UnavailableProviders) ==
    /\ InitialStates \subseteq S
    /\ InvA \subseteq S
    /\ InvB \subseteq S
    /\ RelationTyped(S, StepA)
    /\ RelationTyped(S, StepB)
    /\ RelationTyped(S, SharedSteps)
    /\ RelationTyped(S, EnvironmentSteps)
    /\ RelationTyped(S, InterferenceSteps)
    /\ RelyGuaranteeTyped(S, RelyA, StepA)
    /\ RelyGuaranteeTyped(S, RelyB, StepB)
    /\ FailureModelTyped(
           S, FailureSteps, UnavailableProviders, Providers)
    /\ InterferenceSteps \subseteq
         ComposedSteps(
             StepA, StepB, SharedSteps,
             EnvironmentSteps, FailureSteps)

CrossSafetyUnderAcyclicRelies(
        S, InvA, InvB, StepA, StepB,
        RelyA, RelyB, RelyEdges) ==
    /\ IF <<"component-a", "component-b">> \in RelyEdges
          THEN /\ StepB \subseteq RelyA
               /\ Stable(S, InvA, RelyA)
          ELSE Stable(S, InvA, StepB)
    /\ IF <<"component-b", "component-a">> \in RelyEdges
          THEN /\ StepA \subseteq RelyB
               /\ Stable(S, InvB, RelyB)
          ELSE Stable(S, InvB, StepA)

CommonTransitionsPreserveJoint(
        S, InvA, InvB,
        SharedSteps, EnvironmentSteps, FailureSteps) ==
    LET Joint == JointInvariant(InvA, InvB)
    IN
    /\ Stable(S, Joint, SharedSteps)
    /\ Stable(S, Joint, EnvironmentSteps)
    /\ Stable(S, Joint, FailureSteps)

AcyclicSafetyClosure(
        S, InitialStates, InvA, InvB,
        StepA, StepB, SharedSteps,
        EnvironmentSteps, FailureSteps,
        RelyA, RelyB, RelyEdges) ==
    /\ AcyclicRelyGraph(RelyEdges)
    /\ Initializes(InitialStates, InvA)
    /\ Initializes(InitialStates, InvB)
    /\ Stable(S, InvA, StepA)
    /\ Stable(S, InvB, StepB)
    /\ CrossSafetyUnderAcyclicRelies(
           S, InvA, InvB, StepA, StepB,
           RelyA, RelyB, RelyEdges)
    /\ CommonTransitionsPreserveJoint(
           S, InvA, InvB,
           SharedSteps, EnvironmentSteps, FailureSteps)

MutualSafetyDischarge(
        S, InitialStates, InvA, InvB,
        StepA, StepB, SharedSteps,
        EnvironmentSteps, FailureSteps,
        RelyA, RelyB, RelyEdges) ==
    /\ CyclicRelyGraph(RelyEdges)
    /\ PeerReliesDischarged(S, StepA, StepB, RelyA, RelyB)
    /\ MutualSafetyClosure(
           S, InitialStates, JointInvariant(InvA, InvB),
           StepA, StepB, SharedSteps,
           EnvironmentSteps \cup FailureSteps)

CompositionSafetyPremises(
        S, InitialStates, InvA, InvB,
        StepA, StepB, SharedSteps,
        EnvironmentSteps, FailureSteps, InterferenceSteps,
        RelyA, RelyB, RelyEdges,
        Providers, UnavailableProviders) ==
    /\ CompositionBoundaryPremises(
           S, InitialStates, InvA, InvB,
           StepA, StepB, SharedSteps,
           EnvironmentSteps, FailureSteps, InterferenceSteps,
           RelyA, RelyB, Providers, UnavailableProviders)
    /\ \/ AcyclicSafetyClosure(
              S, InitialStates, InvA, InvB,
              StepA, StepB, SharedSteps,
              EnvironmentSteps, FailureSteps,
              RelyA, RelyB, RelyEdges)
       \/ MutualSafetyDischarge(
              S, InitialStates, InvA, InvB,
              StepA, StepB, SharedSteps,
              EnvironmentSteps, FailureSteps,
              RelyA, RelyB, RelyEdges)

CompositionSafetyConclusion(
        S, InitialStates, InvA, InvB,
        StepA, StepB, SharedSteps,
        EnvironmentSteps, FailureSteps, InterferenceSteps) ==
    LET Joint == JointInvariant(InvA, InvB)
        AllSteps == ComposedSteps(
            StepA, StepB, SharedSteps,
            EnvironmentSteps, FailureSteps)
    IN
    /\ Initializes(InitialStates, Joint)
    /\ Stable(S, Joint, AllSteps)
    /\ Stable(S, Joint, InterferenceSteps)

====
