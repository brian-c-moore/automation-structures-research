---- MODULE OwnershipAssuranceKernel_Proof ----
EXTENDS OwnershipAssuranceKernel, TLAPS

CONSTANTS AssuranceStateDomain, AssuranceActors, AssuranceProviders,
          AssuranceClaimant, AssuranceCommitOwner,
          AssuranceCommitDelegate,
          KernelAssuranceProvider, KernelAssurancePosition,
          KernelPreventionControllers, AssuranceFailureSteps,
          AssuranceUnavailableProviders,
          AssurancePersistentEvidenceObserve,
          KernelPersistentEvidence, KernelRecoveryAvailable

THEOREM OwnershipAssuranceClassification ==
    AssuranceBoundaryTyped(
        AssuranceStateDomain, AssuranceActors, AssuranceProviders,
        AssuranceClaimant, AssuranceCommitOwner,
        AssuranceCommitDelegate,
        KernelAssuranceProvider, KernelAssurancePosition,
        KernelPreventionControllers, AssuranceFailureSteps,
        AssuranceUnavailableProviders,
        AssurancePersistentEvidenceObserve,
        KernelPersistentEvidence, KernelRecoveryAvailable)
    => OwnershipAssuranceCeiling(
           AssuranceClaimant, AssuranceCommitOwner,
           KernelAssuranceProvider, KernelAssurancePosition,
           KernelPreventionControllers, AssuranceUnavailableProviders,
           KernelPersistentEvidence, KernelRecoveryAvailable)
BY SMT DEF AssuranceBoundaryTyped, AssuranceHealthy,
           PreventionSupported, DetectionSupported, RecoverySupported,
           GuaranteeCeiling, OwnershipAssuranceCeiling,
           AssurancePositions, GuaranteeKinds,
           FailureModelTyped, RelationTyped, Pairs

====
