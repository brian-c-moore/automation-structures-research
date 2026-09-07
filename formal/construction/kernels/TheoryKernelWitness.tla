---- MODULE TheoryKernelWitness ----
EXTENDS TheoryKernel

States == {"idle", "checked", "committed", "bad"}

InitialStates == {"idle"}
ObligationStates == States \ {"bad"}

SystemSteps ==
    {<<"idle", "checked">>,
     <<"checked", "committed">>,
     <<"committed", "committed">>}

EnvironmentSteps == IdentityRelation(States)
RelySteps == EnvironmentSteps

ObligationWitnessPremises ==
    ObligationPreservationPremises(
        States, InitialStates, ObligationStates,
        SystemSteps, EnvironmentSteps, RelySteps)

ObligationWitnessConclusion ==
    ObligationPreservationConclusion(
        States, InitialStates, ObligationStates,
        SystemSteps, EnvironmentSteps)

StableCheckResults == {"checked"}
StablePredicateStates == {"checked"}
StableInterferenceSteps == {<<"checked", "checked">>}
StableCommitSteps == {<<"checked", "committed">>}

StableCheckActWitnessPremises ==
    CheckActAdmission(
        States, "stable", StableCheckResults, StablePredicateStates,
        StableInterferenceSteps, StableCommitSteps)

StableCheckActWitnessConclusion ==
    CheckActLicensed(States, StablePredicateStates, StableCommitSteps)

AtomicPredicateStates == {"idle"}
AtomicCheckResults == {"idle"}
AtomicCommitSteps == {<<"idle", "committed">>}

AtomicCheckActWitnessPremises ==
    CheckActAdmission(
        States, "atomic", AtomicCheckResults, AtomicPredicateStates,
        {}, AtomicCommitSteps)

AtomicCheckActWitnessConclusion ==
    CheckActLicensed(States, AtomicPredicateStates, AtomicCommitSteps)

RejectsEmptyAtomicCommit ==
    ~AtomicCheckActPremises(
        States, AtomicCheckResults, AtomicPredicateStates, {})

VARIABLE witness

vars == <<witness>>

Init == witness = 0

Next == UNCHANGED vars

Spec == Init /\ [][Next]_vars

====
