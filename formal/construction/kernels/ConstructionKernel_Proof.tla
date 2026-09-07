---- MODULE ConstructionKernel_Proof ----
EXTENDS ConstructionKernel,
        TheoryKernel_Proof,
        OwnershipAssuranceKernel_Proof,
        CompositionKernel_Proof,
        RefinementKernel_Proof,
        TLAPS

CONSTANTS RetainedStructures, SelectedStructures,
          RetainedExecutionCarriers, SelectedExecutionCarrier,
          Instances, StructureOf, ParameterDomain,
          ParameterDomainOf, Parameters,
          SelectedFamilies, DeclaredGlobalAssumptions,
          LibraryPremises, DeploymentPremises, DischargedPremises,
          RegisteredGuarantees, BoundaryIds, FailureCeilings,
          GuaranteeFamily, GuaranteeKindOf, GuaranteePropertyClass,
          GuaranteeBoundaryOf, GuaranteeFailureCeilingOf,
          ImplementationCommitSteps, FormalCommitSteps,
          ImplementationFailureSteps, FormalFailureSteps,
          DeploymentSteps, FormalEnvironmentSteps, TrustedSteps,
          ImplementationCommitOwner, FormalCommitOwner,
          ImplementationCommitDelegate, FormalCommitDelegate,
          ImplementationCommitAssurance, FormalCommitAssurance,
          ImplementationPersistentObserve, FormalPersistentObserve,
          EvidenceEvents, EvidenceSubjects, EvidenceCommitActionLinks,
          EventObservation, EventSubject, EventAction,
          EventClaimant, EventOwner, EventCommit,
          EventAssurance, EventEvidenceClass

ObligationFamilyPremises ==
    ObligationPreservationPremises(
        ObligationStateDomain, ObligationInitialStates,
        RegisteredObligationStates, ObligationSystemSteps,
        ObligationEnvironmentSteps, ObligationRelySteps)

ObligationFamilyConclusion ==
    ObligationPreservationConclusion(
        ObligationStateDomain, ObligationInitialStates,
        RegisteredObligationStates, ObligationSystemSteps,
        ObligationEnvironmentSteps)

CheckActFamilyPremises ==
    CheckActAdmission(
        ObligationStateDomain, KernelCheckActMode,
        KernelCheckResultStates, KernelPredicateStates,
        KernelInterferenceSteps, KernelGovernedCommitSteps)

CheckActFamilyConclusion ==
    CheckActLicensed(
        ObligationStateDomain, KernelPredicateStates,
        KernelGovernedCommitSteps)

ProgressFamilyPremises == Premises /\ Spec

ProgressFamilyConclusion ==
    EventualRankedClosure(ProgressClosedStates)

OwnershipAssuranceFamilyPremises ==
    AssuranceBoundaryTyped(
        AssuranceStateDomain, AssuranceActors, AssuranceProviders,
        AssuranceClaimant, AssuranceCommitOwner,
        AssuranceCommitDelegate,
        KernelAssuranceProvider, KernelAssurancePosition,
        KernelPreventionControllers, AssuranceFailureSteps,
        AssuranceUnavailableProviders,
        AssurancePersistentEvidenceObserve,
        KernelPersistentEvidence, KernelRecoveryAvailable)

OwnershipAssuranceFamilyConclusion ==
    OwnershipAssuranceCeiling(
        AssuranceClaimant, AssuranceCommitOwner,
        KernelAssuranceProvider, KernelAssurancePosition,
        KernelPreventionControllers, AssuranceUnavailableProviders,
        KernelPersistentEvidence, KernelRecoveryAvailable)

CompositionFamilyPremises ==
    CompositionSafetyPremises(
        CompositionStateDomain, CompositionInitialStates,
        CompositionInvA, CompositionInvB,
        CompositionStepA, CompositionStepB, CompositionSharedSteps,
        CompositionEnvironmentSteps, CompositionFailureSteps,
        CompositionInterferenceSteps,
        CompositionRelyA, CompositionRelyB, CompositionRelyEdges,
        CompositionProviders, CompositionUnavailableProviders)

CompositionFamilyConclusion ==
    CompositionSafetyConclusion(
        CompositionStateDomain, CompositionInitialStates,
        CompositionInvA, CompositionInvB,
        CompositionStepA, CompositionStepB, CompositionSharedSteps,
        CompositionEnvironmentSteps, CompositionFailureSteps,
        CompositionInterferenceSteps)

RefinementFamilyPremises ==
    RefinementTransferPremises(
        SelectedClasses,
        ProgressStates, ProgressActiveStates, ProgressClosedStates,
        FormalStates,
        ImplementationInitial, FormalInitial,
        ImplementationSteps, FormalSteps, FormalSafeStates,
        FormalObservationStates, ObservationDomain, AllowedObservations,
        Abstraction, ImplementationObserve, FormalObserve,
        FormalClosedStates, FormalProgressSteps, FormalOtherSteps,
        DecreasingSteps, NonprogressSteps,
        ProgressRankBound, FormalRank, ProgressRank,
        ProgressFairnessOwners, ProgressFairnessOwner,
        FormalFairnessOwnerOf, ProgressFairnessOwnerOf)

RefinementFamilyConclusion ==
    RefinementTransferConclusion(
        SelectedClasses,
        ProgressStates, ProgressClosedStates,
        ImplementationInitial,
        ImplementationSteps, FormalSafeStates,
        FormalObservationStates, AllowedObservations,
        Abstraction, ImplementationObserve)

KernelImplementationConformance ==
    /\ ProgressStates # {}
    /\ FormalStates # {}
    /\ CheckableImplementationConformance(
           ProgressStates, FormalStates,
           ImplementationInitial, FormalInitial,
           ImplementationSteps, FormalSteps,
           ImplementationCommitSteps, FormalCommitSteps,
           ImplementationFailureSteps, FormalFailureSteps,
           DecreasingSteps, FormalProgressSteps,
           DeploymentSteps, FormalEnvironmentSteps,
           TrustedSteps, ObservationDomain,
           ImplementationCommitOwner, FormalCommitOwner,
           ImplementationCommitDelegate, FormalCommitDelegate,
           ImplementationCommitAssurance, FormalCommitAssurance,
           ImplementationPersistentObserve, FormalPersistentObserve,
           Abstraction, ImplementationObserve, FormalObserve)

KernelSupportedGuaranteeKinds ==
    GuaranteeCeiling(
        AssuranceClaimant, AssuranceCommitOwner,
        KernelAssuranceProvider, KernelAssurancePosition,
        KernelPreventionControllers, AssuranceUnavailableProviders,
        KernelPersistentEvidence, KernelRecoveryAvailable)

KernelSemanticCoherence ==
    /\ StateStepBoundaryCoherence(
           SelectedFamilies,
           FormalStates, FormalInitial, FormalSteps, FormalSafeStates,
           FormalCommitSteps, FormalFailureSteps,
           FormalEnvironmentSteps,
           FormalCommitOwner, FormalCommitDelegate,
           FormalCommitAssurance, FormalPersistentObserve,
           ObligationStateDomain, ObligationInitialStates,
           RegisteredObligationStates, ObligationSystemSteps,
           ObligationEnvironmentSteps, KernelInterferenceSteps,
           KernelGovernedCommitSteps,
           AssuranceStateDomain, AssuranceActors, AssuranceClaimant,
           AssuranceCommitOwner,
           AssuranceCommitDelegate,
           AssuranceFailureSteps, AssuranceUnavailableProviders,
           AssurancePersistentEvidenceObserve,
           KernelAssurancePosition,
           CompositionStateDomain, CompositionInitialStates,
           CompositionInvA, CompositionInvB,
           CompositionStepA, CompositionStepB,
           CompositionSharedSteps, CompositionEnvironmentSteps,
           CompositionFailureSteps, CompositionUnavailableProviders)
    /\ ProgressRefinementCoherence(
           SelectedFamilies, SelectedClasses,
           ProgressStates, ImplementationSteps,
           DecreasingSteps, NonprogressSteps,
           ProgressClosedStates,
           FormalStates, FormalClosedStates, Abstraction)
    /\ RegistrationBoundaryCoherence(
           RegisteredGuarantees, BoundaryIds, FailureCeilings,
           GuaranteeBoundaryOf, GuaranteeFailureCeilingOf,
           FormalStates, FormalCommitSteps, FormalFailureSteps,
           FormalObserve, AssuranceUnavailableProviders)
    /\ RefinementRegistrationCoherence(
           RegisteredGuarantees, GuaranteeFamily,
           GuaranteePropertyClass, SelectedClasses)
    /\ EvidenceRegistrationCoherence(
           RegisteredGuarantees, GuaranteePropertyClass,
           KernelSupportedGuaranteeKinds,
           EvidenceEvents, ObservationDomain, EvidenceSubjects,
           AssuranceActors, FormalSteps, FormalCommitSteps,
           EvidenceCommitActionLinks,
           EventObservation, EventSubject, EventAction,
           EventClaimant, EventOwner, EventCommit,
           EventAssurance, EventEvidenceClass,
           FormalCommitOwner, FormalCommitAssurance,
           FormalObserve, FormalPersistentObserve,
           AssuranceClaimant)

ConstructionFamilyPremises ==
    ConstructionAdmitted(
        RetainedStructures, SelectedStructures,
        RetainedExecutionCarriers, SelectedExecutionCarrier,
        Instances, StructureOf, ParameterDomain,
        ParameterDomainOf, Parameters,
        SelectedFamilies, DeclaredGlobalAssumptions,
        LibraryPremises, DeploymentPremises, DischargedPremises,
        RegisteredGuarantees, BoundaryIds, FailureCeilings,
        GuaranteeFamily, GuaranteeKindOf, GuaranteePropertyClass,
        GuaranteeBoundaryOf, GuaranteeFailureCeilingOf,
        KernelSupportedGuaranteeKinds, KernelSemanticCoherence,
        KernelImplementationConformance,
        ObligationFamilyPremises, CheckActFamilyPremises,
        ProgressFamilyPremises,
        OwnershipAssuranceFamilyPremises, CompositionFamilyPremises,
        RefinementFamilyPremises)

ConstructionFamilyConclusion ==
    RegisteredConstructionGuaranteeBundle(
        RetainedStructures, SelectedStructures,
        Instances, StructureOf, ParameterDomain,
        ParameterDomainOf, Parameters,
        SelectedFamilies,
        RegisteredGuarantees, BoundaryIds, FailureCeilings,
        GuaranteeFamily, GuaranteeKindOf, GuaranteePropertyClass,
        GuaranteeBoundaryOf, GuaranteeFailureCeilingOf,
        KernelSupportedGuaranteeKinds,
        ObligationFamilyConclusion, CheckActFamilyConclusion,
        ProgressFamilyConclusion,
        OwnershipAssuranceFamilyConclusion, CompositionFamilyConclusion,
        RefinementFamilyConclusion)

THEOREM BoundedConstructionSufficiency ==
    ConstructionFamilyPremises => ConstructionFamilyConclusion
BY ObligationPreservation, CheckActStability, RankedProgress,
   OwnershipAssuranceClassification, CompositionSafety,
   ClassSpecificRefinementTransfer
   DEF ConstructionFamilyPremises, ConstructionFamilyConclusion,
       ConstructionAdmitted, RegisteredConstructionGuaranteeBundle,
       ConstructionStaticAdmission, ApplicableKernelClaims,
       GuaranteeRegistrationCompatible,
       ObligationFamilyPremises, ObligationFamilyConclusion,
       CheckActFamilyPremises, CheckActFamilyConclusion,
       ProgressFamilyPremises, ProgressFamilyConclusion,
       OwnershipAssuranceFamilyPremises,
       OwnershipAssuranceFamilyConclusion,
       CompositionFamilyPremises, CompositionFamilyConclusion,
       RefinementFamilyPremises, RefinementFamilyConclusion

====
