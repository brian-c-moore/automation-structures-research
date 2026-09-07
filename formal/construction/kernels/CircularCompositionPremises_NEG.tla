---- MODULE CircularCompositionPremises_NEG ----
EXTENDS CompositionKernel, TLC

States == {"safe", "bad-a"}
InitialStates == {"safe"}
InvA == {"safe"}
InvB == States

StepA == {<<"safe", "safe">>}
StepB == {<<"safe", "bad-a">>}
SharedSteps == {}
EnvironmentSteps == {}
FailureSteps == {}
InterferenceSteps == StepA \cup StepB

RelyA == StepB
RelyB == StepA
RelyEdges == PossibleRelyEdges
Providers == {"runtime"}
UnavailableProviders == {}

PeerReferences ==
    /\ PeerReliesDischarged(
           States, StepA, StepB, RelyA, RelyB)
    /\ CyclicRelyGraph(RelyEdges)

SchemaRejectsCircularity ==
    ~CompositionSafetyPremises(
        States, InitialStates, InvA, InvB,
        StepA, StepB, SharedSteps,
        EnvironmentSteps, FailureSteps, InterferenceSteps,
        RelyA, RelyB, RelyEdges,
        Providers, UnavailableProviders)

VARIABLE state

vars == <<state>>

Init == state \in InitialStates

BreakA ==
    /\ state = "safe"
    /\ state' = "bad-a"

Next == BreakA \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

JointInvariantHeld == state \in JointInvariant(InvA, InvB)

====
