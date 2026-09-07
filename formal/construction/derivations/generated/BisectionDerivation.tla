---- MODULE BisectionDerivation ----
EXTENDS BisectionDerivationData, TLC

BisectionRecordAccepted == DerivationRecordAccepted(Derivation)

BisectionKernelObligationPremises ==
    ObligationPreservationPremises(
        Derivation.witnessStates, Derivation.witnessInitial,
        Derivation.witnessObligationStates, Derivation.witnessSystemSteps,
        Derivation.witnessEnvironmentSteps, Derivation.witnessRelySteps)

BisectionKernelOwnershipPremises ==
    AssuranceBoundaryTyped(
        Derivation.witnessStates, Derivation.witnessActors,
        Derivation.witnessProviders, Derivation.witnessClaimant,
        Derivation.witnessCommitOwner, Derivation.witnessCommitDelegate,
        Derivation.witnessAssuranceProvider, Derivation.witnessAssurancePosition,
        Derivation.witnessPreventionControllers, Derivation.witnessFailureSteps,
        Derivation.witnessUnavailableProviders, Derivation.witnessPersistentObserve,
        Derivation.witnessPersistentEvidence, Derivation.witnessRecoveryAvailable)

BisectionKernelCheckActPremises ==
    CheckActAdmission(
        Derivation.witnessStates, Derivation.witnessCheckActMode,
        Derivation.witnessCheckResultStates, Derivation.witnessPredicateStates,
        Derivation.witnessInterferenceSteps, Derivation.witnessCommitSteps)

BisectionKernelProgressPremises ==
    RankedProgressPremises(
        Derivation.witnessStates, Derivation.witnessActiveStates,
        Derivation.witnessClosedStates, Derivation.witnessProgressSteps,
        Derivation.witnessOtherSteps, Derivation.witnessRankBound,
        Derivation.witnessRank, Derivation.witnessFairnessOwners,
        Derivation.witnessFairnessOwner, Derivation.witnessFairnessOwnerOf)

DerivationInit == progressState = "Bisection-derivation"
DerivationNext == UNCHANGED progressState
DerivationSpec == DerivationInit /\ [][DerivationNext]_progressVars

====
