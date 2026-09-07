---- MODULE FailureInterferenceOmission_NEG ----
EXTENDS CompositionKernel, TLC

States == {"safe", "failed"}
InitialStates == {"safe"}
InvA == {"safe"}
InvB == States

StepA == {<<"safe", "safe">>}
StepB == {<<"safe", "safe">>}
SharedSteps == {}
EnvironmentSteps == {}
FailureSteps == {<<"safe", "failed">>}
InterferenceSteps == FailureSteps

RelyA == {}
RelyB == {}
RelyEdges == {}
Providers == {"runtime"}
UnavailableProviders == {}

MutantPremises ==
    CompositionSafetyPremises(
        States, InitialStates, InvA, InvB,
        StepA, StepB, SharedSteps,
        EnvironmentSteps, {}, {},
        RelyA, RelyB, RelyEdges,
        Providers, UnavailableProviders)

SchemaRejectsActualBoundary ==
    ~CompositionSafetyPremises(
        States, InitialStates, InvA, InvB,
        StepA, StepB, SharedSteps,
        EnvironmentSteps, FailureSteps, InterferenceSteps,
        RelyA, RelyB, RelyEdges,
        Providers, UnavailableProviders)

VARIABLE state

vars == <<state>>

Init == state \in InitialStates

Failure ==
    /\ state = "safe"
    /\ state' = "failed"

Next == Failure \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

JointInvariantHeld == state \in JointInvariant(InvA, InvB)

====
