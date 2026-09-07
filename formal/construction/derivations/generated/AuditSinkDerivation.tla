---- MODULE AuditSinkDerivation ----
EXTENDS AuditSinkDerivationData, TLC

AuditRecordAccepted == DerivationRecordAccepted(Derivation)

AuditKernelObligationPremises ==
    ObligationPreservationPremises(
        Derivation.witnessStates, Derivation.witnessInitial,
        Derivation.witnessObligationStates,
        Derivation.witnessSystemSteps,
        Derivation.witnessEnvironmentSteps,
        Derivation.witnessRelySteps)

AuditKernelObligationConclusion ==
    ObligationPreservationConclusion(
        Derivation.witnessStates, Derivation.witnessInitial,
        Derivation.witnessObligationStates,
        Derivation.witnessSystemSteps,
        Derivation.witnessEnvironmentSteps)

AuditKernelOwnershipPremises ==
    AssuranceBoundaryTyped(
        Derivation.witnessStates, Derivation.witnessActors,
        Derivation.witnessProviders, Derivation.witnessClaimant,
        Derivation.witnessCommitOwner, Derivation.witnessCommitDelegate,
        Derivation.witnessAssuranceProvider,
        Derivation.witnessAssurancePosition,
        Derivation.witnessPreventionControllers,
        Derivation.witnessFailureSteps,
        Derivation.witnessUnavailableProviders,
        Derivation.witnessPersistentObserve,
        Derivation.witnessPersistentEvidence,
        Derivation.witnessRecoveryAvailable)

AuditKernelOwnershipConclusion ==
    OwnershipAssuranceCeiling(
        Derivation.witnessClaimant, Derivation.witnessCommitOwner,
        Derivation.witnessAssuranceProvider,
        Derivation.witnessAssurancePosition,
        Derivation.witnessPreventionControllers,
        Derivation.witnessUnavailableProviders,
        Derivation.witnessPersistentEvidence,
        Derivation.witnessRecoveryAvailable)

HashCRAssignedToDeployment ==
    /\ "HashCR" \in Derivation.deploymentPremises
    /\ "HashCR" \notin Derivation.libraryPremises

RecordLossSteps == {<<"recorded", "lost">>}

RejectsRecordLossPersistenceOverclaim ==
    ~PersistentAcross(
        Derivation.witnessStates,
        Derivation.witnessPersistentObserve,
        RecordLossSteps)

DerivationInit == progressState = "audit-derivation"
DerivationNext == UNCHANGED progressState
DerivationSpec == DerivationInit /\ [][DerivationNext]_progressVars

====
