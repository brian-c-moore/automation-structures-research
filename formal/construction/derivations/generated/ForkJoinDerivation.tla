---- MODULE ForkJoinDerivation ----
EXTENDS ForkJoinDerivationData, TLC

ForkJoinRecordAccepted == DerivationRecordAccepted(Derivation)

ForkJoinKernelObligationPremises ==
    ObligationPreservationPremises(
        Derivation.witnessStates, Derivation.witnessInitial,
        Derivation.witnessObligationStates, Derivation.witnessSystemSteps,
        Derivation.witnessEnvironmentSteps, Derivation.witnessRelySteps)

ForkJoinKernelOwnershipPremises ==
    AssuranceBoundaryTyped(
        Derivation.witnessStates, Derivation.witnessActors,
        Derivation.witnessProviders, Derivation.witnessClaimant,
        Derivation.witnessCommitOwner, Derivation.witnessCommitDelegate,
        Derivation.witnessAssuranceProvider, Derivation.witnessAssurancePosition,
        Derivation.witnessPreventionControllers, Derivation.witnessFailureSteps,
        Derivation.witnessUnavailableProviders, Derivation.witnessPersistentObserve,
        Derivation.witnessPersistentEvidence, Derivation.witnessRecoveryAvailable)

ForkJoinKernelCheckActPremises ==
    CheckActAdmission(
        Derivation.witnessStates, Derivation.witnessCheckActMode,
        Derivation.witnessCheckResultStates, Derivation.witnessPredicateStates,
        Derivation.witnessInterferenceSteps, Derivation.witnessCommitSteps)

DerivationInit == progressState = "ForkJoin-derivation"
DerivationNext == UNCHANGED progressState
DerivationSpec == DerivationInit /\ [][DerivationNext]_progressVars

====
