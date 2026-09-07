---- MODULE BisectionDerivation_Proof ----
EXTENDS BisectionDerivation, Bisection_Proof, TLAPS

LOCAL ObligationKernel == INSTANCE TheoryKernel_Proof WITH
    ObligationStateDomain <- Derivation.witnessStates,
    ObligationInitialStates <- Derivation.witnessInitial,
    RegisteredObligationStates <- Derivation.witnessObligationStates,
    ObligationSystemSteps <- Derivation.witnessSystemSteps,
    ObligationEnvironmentSteps <- Derivation.witnessEnvironmentSteps,
    ObligationRelySteps <- Derivation.witnessRelySteps,
    KernelCheckActMode <- Derivation.witnessCheckActMode,
    KernelCheckResultStates <- Derivation.witnessCheckResultStates,
    KernelPredicateStates <- Derivation.witnessPredicateStates,
    KernelInterferenceSteps <- Derivation.witnessInterferenceSteps,
    KernelGovernedCommitSteps <- Derivation.witnessCommitSteps

LOCAL OwnershipKernel == INSTANCE OwnershipAssuranceKernel_Proof WITH
    AssuranceStateDomain <- Derivation.witnessStates,
    AssuranceActors <- Derivation.witnessActors,
    AssuranceProviders <- Derivation.witnessProviders,
    AssuranceClaimant <- Derivation.witnessClaimant,
    AssuranceCommitOwner <- Derivation.witnessCommitOwner,
    AssuranceCommitDelegate <- Derivation.witnessCommitDelegate,
    KernelAssuranceProvider <- Derivation.witnessAssuranceProvider,
    KernelAssurancePosition <- Derivation.witnessAssurancePosition,
    KernelPreventionControllers <- Derivation.witnessPreventionControllers,
    AssuranceFailureSteps <- Derivation.witnessFailureSteps,
    AssuranceUnavailableProviders <- Derivation.witnessUnavailableProviders,
    AssurancePersistentEvidenceObserve <- Derivation.witnessPersistentObserve,
    KernelPersistentEvidence <- Derivation.witnessPersistentEvidence,
    KernelRecoveryAvailable <- Derivation.witnessRecoveryAvailable

LOCAL ProgressKernel == INSTANCE ProgressKernel_Proof WITH
    ProgressStates <- Derivation.witnessStates,
    ProgressActiveStates <- Derivation.witnessActiveStates,
    ProgressClosedStates <- Derivation.witnessClosedStates,
    DecreasingSteps <- Derivation.witnessProgressSteps,
    NonprogressSteps <- Derivation.witnessOtherSteps,
    ProgressRankBound <- Derivation.witnessRankBound,
    ProgressRank <- Derivation.witnessRank,
    ProgressFairnessOwners <- Derivation.witnessFairnessOwners,
    ProgressFairnessOwner <- Derivation.witnessFairnessOwner,
    ProgressFairnessOwnerOf <- Derivation.witnessFairnessOwnerOf

THEOREM BisectionLocalDischarge == Spec => []Inv
BY Safety

THEOREM BisectionObligationKernelDischarge ==
    ObligationKernel!ObligationPreservationPremises(
        Derivation.witnessStates, Derivation.witnessInitial,
        Derivation.witnessObligationStates, Derivation.witnessSystemSteps,
        Derivation.witnessEnvironmentSteps, Derivation.witnessRelySteps)
    => ObligationKernel!ObligationPreservationConclusion(
           Derivation.witnessStates, Derivation.witnessInitial,
           Derivation.witnessObligationStates, Derivation.witnessSystemSteps,
           Derivation.witnessEnvironmentSteps)
BY ObligationKernel!ObligationPreservation

THEOREM BisectionOwnershipKernelDischarge ==
    OwnershipKernel!AssuranceBoundaryTyped(
        Derivation.witnessStates, Derivation.witnessActors,
        Derivation.witnessProviders, Derivation.witnessClaimant,
        Derivation.witnessCommitOwner, Derivation.witnessCommitDelegate,
        Derivation.witnessAssuranceProvider, Derivation.witnessAssurancePosition,
        Derivation.witnessPreventionControllers, Derivation.witnessFailureSteps,
        Derivation.witnessUnavailableProviders, Derivation.witnessPersistentObserve,
        Derivation.witnessPersistentEvidence, Derivation.witnessRecoveryAvailable)
    => OwnershipKernel!OwnershipAssuranceCeiling(
           Derivation.witnessClaimant, Derivation.witnessCommitOwner,
           Derivation.witnessAssuranceProvider, Derivation.witnessAssurancePosition,
           Derivation.witnessPreventionControllers,
           Derivation.witnessUnavailableProviders,
           Derivation.witnessPersistentEvidence, Derivation.witnessRecoveryAvailable)
BY OwnershipKernel!OwnershipAssuranceClassification

THEOREM BisectionAdditionalLocalDischarge1 == Spec => Halving
BY HalvingProperty

THEOREM BisectionCheckActKernelDischarge ==
    ObligationKernel!CheckActAdmission(
        Derivation.witnessStates, Derivation.witnessCheckActMode,
        Derivation.witnessCheckResultStates, Derivation.witnessPredicateStates,
        Derivation.witnessInterferenceSteps, Derivation.witnessCommitSteps)
    => ObligationKernel!CheckActLicensed(
           Derivation.witnessStates, Derivation.witnessPredicateStates,
           Derivation.witnessCommitSteps)
BY ObligationKernel!CheckActStability

THEOREM BisectionLocalTemporalDischarge == Spec => EventualConvergence
BY EventualConvergenceProved

THEOREM BisectionProgressKernelDischarge ==
    ProgressKernel!Premises /\ ProgressKernel!Spec
      => ProgressKernel!EventualRankedClosure(
             Derivation.witnessClosedStates)
BY ProgressKernel!RankedProgress

====
