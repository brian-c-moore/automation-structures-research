---- MODULE ProfileFailSafeAdmission_NEG ----
EXTENDS ALKProfileConcreteInstances

AdjacentFailSafeAdmissionHeld ==
    ProfileFailSafeAdmissionHeld("local-reference")

MutantUnavailableAuthorizationHeld ==
    FailSafeAdmission(
        ProfileStates,
        ProfileGovernedCommitSteps("local-reference"),
        ProfileAuthorizedCommitSourceStates("local-reference"), {})

NegativeControlExpected == NegativeControlGate(MutantUnavailableAuthorizationHeld)

====
