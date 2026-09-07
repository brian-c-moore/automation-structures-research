---- MODULE ProfileBypass_NEG ----
EXTENDS ALKProfileConcreteInstances

MutantBypassActions ==
    [ProfilePotentialActions EXCEPT
        !["bypass"] = {<<"open", "closed">>}]
MutantBypassPathClass ==
    [ProfilePathClassOf("local-reference") EXCEPT
        !["local-reference"]["bypass"] = "bypass"]
MutantBypassInputBindingHeld ==
    ExactBypassFailureInputBinding(
        ProfileClaims("local-reference"), ProfileActionLabels,
        MutantBypassActions, ProfileClaimActions("local-reference"),
        MutantBypassPathClass, FALSE)
MutantBypassResult ==
    DerivedFailureCeiling(
        "bypass",
        ProfileDerivedNormalGuaranteeBundle("local-reference"),
        FALSE, TRUE, TRUE, TRUE, TRUE, TRUE, TRUE, TRUE)
MutantBypassNonLostHeld ==
    MutantBypassResult # {"lost"}

NegativeControlExpected == NegativeControlGate(MutantBypassNonLostHeld)

====
