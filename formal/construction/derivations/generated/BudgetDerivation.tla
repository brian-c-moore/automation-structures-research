---- MODULE BudgetDerivation ----
EXTENDS BudgetDerivationData, TLC

BudgetRecordAccepted == DerivationRecordAccepted(Derivation)

BudgetKernelObligationPremises ==
    ObligationPreservationPremises(
        Derivation.witnessStates, Derivation.witnessInitial,
        Derivation.witnessObligationStates,
        Derivation.witnessSystemSteps,
        Derivation.witnessEnvironmentSteps,
        Derivation.witnessRelySteps)

BudgetKernelObligationConclusion ==
    ObligationPreservationConclusion(
        Derivation.witnessStates, Derivation.witnessInitial,
        Derivation.witnessObligationStates,
        Derivation.witnessSystemSteps,
        Derivation.witnessEnvironmentSteps)

BudgetKernelCheckActPremises ==
    CheckActAdmission(
        Derivation.witnessStates, Derivation.witnessCheckActMode,
        Derivation.witnessCheckResultStates,
        Derivation.witnessPredicateStates,
        Derivation.witnessInterferenceSteps,
        Derivation.witnessCommitSteps)

BudgetKernelCheckActConclusion ==
    CheckActLicensed(
        Derivation.witnessStates, Derivation.witnessPredicateStates,
        Derivation.witnessCommitSteps)

BudgetKernelOwnershipPremises ==
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

BudgetKernelOwnershipConclusion ==
    OwnershipAssuranceCeiling(
        Derivation.witnessClaimant, Derivation.witnessCommitOwner,
        Derivation.witnessAssuranceProvider,
        Derivation.witnessAssurancePosition,
        Derivation.witnessPreventionControllers,
        Derivation.witnessUnavailableProviders,
        Derivation.witnessPersistentEvidence,
        Derivation.witnessRecoveryAvailable)

DerivationInit == progressState = "budget-derivation"
DerivationNext == UNCHANGED progressState
DerivationSpec == DerivationInit /\ [][DerivationNext]_progressVars

====
