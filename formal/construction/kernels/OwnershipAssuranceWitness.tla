---- MODULE OwnershipAssuranceWitness ----
EXTENDS OwnershipAssuranceKernel

States == {"boundary"}
Actors == {"claimant", "external-owner", "assurance"}
Providers == {"assurance"}
FailureSteps == {}
PreventionControllers == {"assurance"}
PersistentEvidenceObserve == [state \in States |-> TRUE]

DirectPremises ==
    AssuranceBoundaryTyped(
        States, Actors, Providers,
        "claimant", "claimant", "claimant", "assurance",
        "precommit", PreventionControllers,
        FailureSteps, {}, PersistentEvidenceObserve, TRUE, FALSE)

DirectCeiling ==
    GuaranteeCeiling(
        "claimant", "claimant", "assurance",
        "precommit", PreventionControllers,
        {}, TRUE, FALSE)

DirectPreventionSupported == "prevention" \in DirectCeiling

PostcommitPremises ==
    AssuranceBoundaryTyped(
        States, Actors, Providers,
        "claimant", "external-owner", "external-owner", "assurance",
        "postcommit", PreventionControllers,
        FailureSteps, {}, PersistentEvidenceObserve, TRUE, TRUE)

PostcommitCeiling ==
    GuaranteeCeiling(
        "claimant", "external-owner", "assurance",
        "postcommit", PreventionControllers,
        {}, TRUE, TRUE)

PostcommitDetectionRecoveryOnly ==
    /\ "detection" \in PostcommitCeiling
    /\ "recovery" \in PostcommitCeiling
    /\ "prevention" \notin PostcommitCeiling

UnavailablePremises ==
    AssuranceBoundaryTyped(
        States, Actors, Providers,
        "claimant", "external-owner", "external-owner", "assurance",
        "precommit", PreventionControllers,
        FailureSteps, {"assurance"},
        PersistentEvidenceObserve, TRUE, TRUE)

UnavailableCeiling ==
    GuaranteeCeiling(
        "claimant", "external-owner", "assurance",
        "precommit", PreventionControllers,
        {"assurance"}, TRUE, TRUE)

UnavailableCeilingLimited ==
    UnavailableCeiling \subseteq {"conditional", "lost"}

EvidenceLossStates == {"present", "lost"}
EvidenceLossSteps == {<<"present", "lost">>}
EvidenceLossObserve ==
    [state \in EvidenceLossStates |-> state = "present"]

RejectsUnprovedPersistentEvidence ==
    ~AssuranceBoundaryTyped(
        EvidenceLossStates, Actors, Providers,
        "claimant", "claimant", "claimant", "assurance",
        "at-commit", PreventionControllers,
        EvidenceLossSteps, {}, EvidenceLossObserve, TRUE, FALSE)

VARIABLE witness

vars == <<witness>>

Init == witness = 0
Next == UNCHANGED vars
Spec == Init /\ [][Next]_vars

====
