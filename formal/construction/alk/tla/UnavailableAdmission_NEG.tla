---- MODULE UnavailableAdmission_NEG ----
EXTENDS ALKSemanticModelWitness

FailSafeAdmissionHeld ==
    FailSafeAdmission(
        States, AdmissionSteps, AuthorizedSourceStates, {})

NegativeControlExpected == NegativeControlGate(FailSafeAdmissionHeld)

====
