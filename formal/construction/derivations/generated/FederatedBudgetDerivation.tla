---- MODULE FederatedBudgetDerivation ----
EXTENDS FederatedBudgetDerivationData, TLC

FederatedBudgetRecordAccepted == DerivationRecordAccepted(Derivation)

FederatedBudgetKernelObligationPremises ==
    ObligationPreservationPremises(
        Derivation.witnessStates, Derivation.witnessInitial,
        Derivation.witnessObligationStates, Derivation.witnessSystemSteps,
        Derivation.witnessEnvironmentSteps, Derivation.witnessRelySteps)

FederatedBudgetKernelOwnershipPremises ==
    AssuranceBoundaryTyped(
        Derivation.witnessStates, Derivation.witnessActors,
        Derivation.witnessProviders, Derivation.witnessClaimant,
        Derivation.witnessCommitOwner, Derivation.witnessCommitDelegate,
        Derivation.witnessAssuranceProvider, Derivation.witnessAssurancePosition,
        Derivation.witnessPreventionControllers, Derivation.witnessFailureSteps,
        Derivation.witnessUnavailableProviders, Derivation.witnessPersistentObserve,
        Derivation.witnessPersistentEvidence, Derivation.witnessRecoveryAvailable)

FederatedBudgetKernelCheckActPremises ==
    CheckActAdmission(
        Derivation.witnessStates, Derivation.witnessCheckActMode,
        Derivation.witnessCheckResultStates, Derivation.witnessPredicateStates,
        Derivation.witnessInterferenceSteps, Derivation.witnessCommitSteps)

DerivationInit == progressState = "FederatedBudget-derivation"
DerivationNext == UNCHANGED progressState
DerivationSpec == DerivationInit /\ [][DerivationNext]_progressVars

====
