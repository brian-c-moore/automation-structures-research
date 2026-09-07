---- MODULE PostcommitPreventionOverclaim_NEG ----
EXTENDS OwnershipAssuranceKernel

States == {"boundary"}
Actors == {"claimant", "external-owner", "assurance"}
Providers == {"assurance"}
FailureSteps == {}
PreventionControllers == {"assurance"}
PersistentEvidenceObserve == [state \in States |-> TRUE]

VARIABLE assurance_position

vars == <<assurance_position>>

Init == assurance_position = "precommit"

MoveAssurancePostcommit ==
    /\ assurance_position = "precommit"
    /\ assurance_position' = "postcommit"

Next == MoveAssurancePostcommit \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

BoundaryPremises ==
    AssuranceBoundaryTyped(
        States, Actors, Providers,
        "claimant", "external-owner", "external-owner", "assurance",
        assurance_position, PreventionControllers,
        FailureSteps, {}, PersistentEvidenceObserve, TRUE, TRUE)

CurrentCeiling ==
    GuaranteeCeiling(
        "claimant", "external-owner", "assurance",
        assurance_position, PreventionControllers,
        {}, TRUE, TRUE)

AdvertisedPrevention == "prevention" \in CurrentCeiling

====
