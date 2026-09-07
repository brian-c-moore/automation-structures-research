---- MODULE CompositionKernelWitness ----
EXTENDS CompositionKernel, TLC

States == {"start", "done", "bad-a", "bad-b"}
InitialStates == {"start"}
InvA == {"start", "done", "bad-b"}
InvB == {"start", "done", "bad-a"}

StepA == {<<"start", "done">>}
StepB == {<<"done", "done">>}
SharedSteps == {<<"done", "done">>}
EnvironmentSteps == {<<"start", "start">>}
FailureSteps == {<<"done", "done">>}
InterferenceSteps ==
    ComposedSteps(
        StepA, StepB, SharedSteps,
        EnvironmentSteps, FailureSteps)

Providers == {"runtime"}
UnavailableProviders == {}

AcyclicRelyA == StepB
AcyclicRelyB == {}
AcyclicEdges == {<<"component-a", "component-b">>}

MutualRelyA == StepB
MutualRelyB == StepA
MutualEdges == PossibleRelyEdges

AcyclicPremises ==
    CompositionSafetyPremises(
        States, InitialStates, InvA, InvB,
        StepA, StepB, SharedSteps,
        EnvironmentSteps, FailureSteps, InterferenceSteps,
        AcyclicRelyA, AcyclicRelyB, AcyclicEdges,
        Providers, UnavailableProviders)

MutualPremises ==
    CompositionSafetyPremises(
        States, InitialStates, InvA, InvB,
        StepA, StepB, SharedSteps,
        EnvironmentSteps, FailureSteps, InterferenceSteps,
        MutualRelyA, MutualRelyB, MutualEdges,
        Providers, UnavailableProviders)

AcyclicConclusion ==
    CompositionSafetyConclusion(
        States, InitialStates, InvA, InvB,
        StepA, StepB, SharedSteps,
        EnvironmentSteps, FailureSteps, InterferenceSteps)

MutualConclusion == AcyclicConclusion

VARIABLE state

vars == <<state>>

Init == state \in InitialStates

Advance ==
    /\ state = "start"
    /\ state' = "done"

RemainDone ==
    /\ state = "done"
    /\ state' = "done"

Next == Advance \/ RemainDone

Spec == Init /\ [][Next]_vars

JointInvariantHeld == state \in JointInvariant(InvA, InvB)

====
