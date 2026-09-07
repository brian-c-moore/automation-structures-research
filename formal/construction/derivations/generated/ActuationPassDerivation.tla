---- MODULE ActuationPassDerivation ----
EXTENDS ActuationPassDerivationData, TLC

ActuationRecordAccepted == DerivationRecordAccepted(Derivation)

ActuationKernelObligationPremises ==
    ObligationPreservationPremises(
        Derivation.witnessStates, Derivation.witnessInitial,
        Derivation.witnessObligationStates,
        Derivation.witnessSystemSteps,
        Derivation.witnessEnvironmentSteps,
        Derivation.witnessRelySteps)

ActuationKernelObligationConclusion ==
    ObligationPreservationConclusion(
        Derivation.witnessStates, Derivation.witnessInitial,
        Derivation.witnessObligationStates,
        Derivation.witnessSystemSteps,
        Derivation.witnessEnvironmentSteps)

ActuationKernelCheckActPremises ==
    CheckActAdmission(
        Derivation.witnessStates, Derivation.witnessCheckActMode,
        Derivation.witnessCheckResultStates,
        Derivation.witnessPredicateStates,
        Derivation.witnessInterferenceSteps,
        Derivation.witnessCommitSteps)

ActuationKernelCheckActConclusion ==
    CheckActLicensed(
        Derivation.witnessStates, Derivation.witnessPredicateStates,
        Derivation.witnessCommitSteps)

ActuationKernelOwnershipPremises ==
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

ActuationKernelOwnershipConclusion ==
    OwnershipAssuranceCeiling(
        Derivation.witnessClaimant, Derivation.witnessCommitOwner,
        Derivation.witnessAssuranceProvider,
        Derivation.witnessAssurancePosition,
        Derivation.witnessPreventionControllers,
        Derivation.witnessUnavailableProviders,
        Derivation.witnessPersistentEvidence,
        Derivation.witnessRecoveryAvailable)

EnvironmentPartitionExact ==
    /\ Derivation.systemActions = {"Actuate", "Finish"}
    /\ Derivation.environmentActions = {"Allocate", "Deallocate"}
    /\ Derivation.commitActions = {"Actuate", "Finish"}

EffectSuccessOutsideClaim ==
    "effect-record-fidelity-is-not-proof-of-external-side-effect-success"
        \in Derivation.residuals

DerivationInit == progressState = "actuation-derivation"
DerivationNext == UNCHANGED progressState
DerivationSpec == DerivationInit /\ [][DerivationNext]_progressVars

====
