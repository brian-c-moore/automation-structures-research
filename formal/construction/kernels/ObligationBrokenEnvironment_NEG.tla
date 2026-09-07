---- MODULE ObligationBrokenEnvironment_NEG ----
EXTENDS TheoryKernel

States == {"safe", "violated"}
InitialStates == {"safe"}
ObligationStates == {"safe"}
SystemSteps == {<<"safe", "safe">>}
EnvironmentSteps == {<<"safe", "violated">>}
RelySteps == {<<"safe", "safe">>}

SchemaRejectsBrokenEnvironment ==
    ~ObligationPreservationPremises(
        States, InitialStates, ObligationStates,
        SystemSteps, EnvironmentSteps, RelySteps)

VARIABLE state

vars == <<state>>

Init == state = "safe"

SystemStep ==
    /\ state = "safe"
    /\ state' = "safe"

EnvironmentBreak ==
    /\ state = "safe"
    /\ state' = "violated"

Next == SystemStep \/ EnvironmentBreak

Spec == Init /\ [][Next]_vars

ObligationHeld == state \in ObligationStates

====
