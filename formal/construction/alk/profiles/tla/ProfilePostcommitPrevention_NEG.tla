---- MODULE ProfilePostcommitPrevention_NEG ----
EXTENDS ALKProfileConcreteInstances

MutantPostcommitCeiling ==
    GuaranteeCeiling(
        "builder", "external-owner", "assurer", "postcommit",
        {}, {}, TRUE, TRUE)
MutantPostcommitPreventionHeld ==
    "prevention" \in MutantPostcommitCeiling

NegativeControlExpected == NegativeControlGate(MutantPostcommitPreventionHeld)

====
