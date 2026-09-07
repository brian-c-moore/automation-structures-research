---- MODULE SequentialDerivation ----
EXTENDS SequentialDerivationData, TLC

SequentialRecordAccepted == DerivationRecordAccepted(Derivation)

SequentialKernelObligationPremises ==
    ObligationPreservationPremises(
        Derivation.witnessStates, Derivation.witnessInitial,
        Derivation.witnessObligationStates,
        Derivation.witnessSystemSteps,
        Derivation.witnessEnvironmentSteps,
        Derivation.witnessRelySteps)

SequentialKernelObligationConclusion ==
    ObligationPreservationConclusion(
        Derivation.witnessStates, Derivation.witnessInitial,
        Derivation.witnessObligationStates,
        Derivation.witnessSystemSteps,
        Derivation.witnessEnvironmentSteps)

SequentialKernelOwnershipPremises ==
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

SequentialKernelOwnershipConclusion ==
    OwnershipAssuranceCeiling(
        Derivation.witnessClaimant, Derivation.witnessCommitOwner,
        Derivation.witnessAssuranceProvider,
        Derivation.witnessAssurancePosition,
        Derivation.witnessPreventionControllers,
        Derivation.witnessUnavailableProviders,
        Derivation.witnessPersistentEvidence,
        Derivation.witnessRecoveryAvailable)

SingleLocusCeilingRecorded ==
    "single-locus-is-a-declared-representation-ceiling-not-a-noninterference-theorem"
        \in Derivation.residuals

NoFalseProgressFamily == "progress" \notin Derivation.applicableFamilies

DerivationInit == progressState = "sequential-derivation"
DerivationNext == UNCHANGED progressState
DerivationSpec == DerivationInit /\ [][DerivationNext]_progressVars

====
