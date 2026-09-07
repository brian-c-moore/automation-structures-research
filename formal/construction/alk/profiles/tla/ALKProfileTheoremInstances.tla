---- MODULE ALKProfileTheoremInstances ----
EXTENDS ALKProfilesWitness, TLAPS

CONSTANT Profile

LOCAL ProfileTheorem == INSTANCE ALKConstructionTheorem_Proof
    WITH ObligationStateDomain <- ProfileStates,
         ObligationInitialStates <- ProfileFormalInitial,
         RegisteredObligationStates <- ProfileSafeStates,
         ObligationSystemSteps <- ProfileObligationSystemSteps(Profile),
         ObligationEnvironmentSteps <-
           ProfileObligationEnvironmentSteps(Profile),
         ObligationRelySteps <- ProfileObligationRelySteps(Profile),
         KernelCheckActMode <- ProfileKernelCheckActMode,
         KernelCheckResultStates <- ProfileKernelCheckResultStates,
         KernelPredicateStates <- ProfileKernelPredicateStates,
         KernelInterferenceSteps <- ProfileKernelInterferenceSteps(Profile),
         KernelGovernedCommitSteps <-
           ProfileKernelGovernedCommitSteps(Profile),

         ProgressStates <- ProfileImplementationStates,
         ProgressActiveStates <- ProfileImplementationActiveStates,
         ProgressClosedStates <- ProfileImplementationClosedStates,
         DecreasingSteps <- ProfileImplementationProgressSteps(Profile),
         NonprogressSteps <- ProfileImplementationOtherSteps(Profile),
         ProgressRankBound <- ProfileRankBound,
         ProgressRank <- ProfileImplementationRank,
         ProgressFairnessOwners <- ProfileFairnessOwners(Profile),
         ProgressFairnessOwner <- ProfileFairnessOwner(Profile),
         ProgressFairnessOwnerOf <-
           ProfileImplementationFairnessOwnerOf(Profile),

         AssuranceStateDomain <- ProfileStates,
         AssuranceActors <- ProfileKernelActors(Profile),
         AssuranceProviders <- ProfileKernelProviders,
         AssuranceClaimant <- ProfileKernelClaimant,
         AssuranceCommitOwner <- ProfileKernelCommitOwner(Profile),
         AssuranceCommitDelegate <- ProfileKernelCommitDelegate(Profile),
         KernelAssuranceProvider <- ProfileKernelAssuranceProvider,
         KernelAssurancePosition <- ProfileKernelAssurancePosition,
         KernelPreventionControllers <- ProfileKernelPreventionControllers,
         AssuranceFailureSteps <- ProfileFormalFailureSteps,
         AssuranceUnavailableProviders <-
           ProfileKernelUnavailableProviders,
         AssurancePersistentEvidenceObserve <-
           ProfileFormalPersistentObserve,
         KernelPersistentEvidence <- ProfileKernelPersistentEvidence,
         KernelRecoveryAvailable <- ProfileKernelRecoveryAvailable,

         CompositionStateDomain <- ProfileStates,
         CompositionInitialStates <- ProfileCompositionInitialStates,
         CompositionInvA <- ProfileCompositionInvA,
         CompositionInvB <- ProfileCompositionInvB,
         CompositionStepA <- ProfileCompositionStepA(Profile),
         CompositionStepB <- ProfileCompositionStepB(Profile),
         CompositionSharedSteps <-
           ProfileCompositionSharedSteps(Profile),
         CompositionEnvironmentSteps <-
           ProfileCompositionEnvironmentSteps(Profile),
         CompositionFailureSteps <- ProfileCompositionFailureSteps,
         CompositionInterferenceSteps <-
           ProfileCompositionInterferenceSteps(Profile),
         CompositionRelyA <- ProfileCompositionRelyA(Profile),
         CompositionRelyB <- ProfileCompositionRelyB(Profile),
         CompositionRelyEdges <- ProfileRelyEdges(Profile),
         CompositionProviders <- ProfileKernelProviders,
         CompositionUnavailableProviders <- {},

         SelectedClasses <- ProfileSelectedClasses,
         FormalStates <- ProfileFormalStates,
         ImplementationInitial <- ProfileImplementationInitial,
         FormalInitial <- ProfileFormalInitial,
         ImplementationSteps <- ProfileImplementationSteps(Profile),
         FormalSteps <- ProfileFormalSteps(Profile),
         FormalSafeStates <- ProfileFormalSafeStates,
         FormalObservationStates <- ProfileFormalObservationStates,
         ObservationDomain <- ProfileObservationDomain,
         AllowedObservations <- ProfileAllowedObservations,
         Abstraction <- ProfileAbstraction,
         ImplementationObserve <- ProfileImplementationObserve,
         FormalObserve <- ProfileFormalObserve,
         FormalClosedStates <- ProfileFormalClosedStates,
         FormalProgressSteps <- ProfileFormalProgressSteps(Profile),
         FormalOtherSteps <- ProfileFormalOtherSteps(Profile),
         FormalRank <- ProfileFormalRank,
         FormalFairnessOwnerOf <- ProfileFormalFairnessOwnerOf(Profile),

         RetainedStructures <- ProfileRetainedStructuresForKernel,
         SelectedStructures <-
           ProfileSelectedStructuresForKernel(Profile),
         RetainedExecutionCarriers <- RetainedExecutionModalityNames,
         SelectedExecutionCarrier <-
           ProfileSelectedExecutionCarrier(Profile),
         Instances <- ProfileInstances(Profile),
         StructureOf <- ProfileStructureOf(Profile),
         ParameterDomain <- ProfileParameterDomain,
         ParameterDomainOf <- ProfileParameterDomainOf(Profile),
         Parameters <- ProfileParameters(Profile),
         SelectedFamilies <- ProfileSelectedFamilies,
         DeclaredGlobalAssumptions <- ProfileDeclaredGlobalAssumptions,
         LibraryPremises <- ProfileLibraryPremises,
         DeploymentPremises <- ProfileDeploymentPremises,
         DischargedPremises <- ProfileDischargedPremises,
         RegisteredGuarantees <- ProfileRegisteredGuarantees,
         BoundaryIds <- ProfileBoundaryIds(Profile),
         FailureCeilings <- ProfileFailureCeilings(Profile),
         GuaranteeFamily <- ProfileGuaranteeFamily,
         GuaranteeKindOf <- ProfileGuaranteeKindOf,
         GuaranteePropertyClass <- ProfileGuaranteePropertyClass,
         GuaranteeBoundaryOf <- ProfileGuaranteeBoundaryOf(Profile),
         GuaranteeFailureCeilingOf <-
           ProfileGuaranteeFailureCeilingOf(Profile),
         ImplementationCommitSteps <-
           ProfileImplementationCommitSteps(Profile),
         FormalCommitSteps <- ProfileFormalCommitSteps(Profile),
         ImplementationFailureSteps <-
           ProfileImplementationFailureSteps,
         FormalFailureSteps <- ProfileFormalFailureSteps,
         DeploymentSteps <- ProfileDeploymentSteps(Profile),
         FormalEnvironmentSteps <-
           ProfileFormalEnvironmentSteps(Profile),
         TrustedSteps <- ProfileTrustedSteps(Profile),
         ImplementationCommitOwner <-
           ProfileImplementationCommitOwner(Profile),
         FormalCommitOwner <- ProfileFormalCommitOwner(Profile),
         ImplementationCommitDelegate <-
           ProfileImplementationCommitDelegate(Profile),
         FormalCommitDelegate <- ProfileFormalCommitDelegate(Profile),
         ImplementationCommitAssurance <-
           ProfileImplementationCommitAssurance(Profile),
         FormalCommitAssurance <-
           ProfileFormalCommitAssurance(Profile),
         ImplementationPersistentObserve <-
           ProfileImplementationPersistentObserve,
         FormalPersistentObserve <- ProfileFormalPersistentObserve,
         EvidenceEvents <- ProfileKernelEvidenceEvents(Profile),
         EvidenceSubjects <- ProfileKernelEvidenceSubjects,
         EvidenceCommitActionLinks <-
           ProfileKernelEvidenceCommitActionLinks(Profile),
         EventObservation <- ProfileKernelEventObservation(Profile),
         EventSubject <- ProfileKernelEventSubject(Profile),
         EventAction <- ProfileKernelEventAction(Profile),
         EventClaimant <- ProfileKernelEventClaimant(Profile),
         EventOwner <- ProfileKernelEventOwner(Profile),
         EventCommit <- ProfileKernelEventCommit(Profile),
         EventAssurance <- ProfileKernelEventAssurance(Profile),
         EventEvidenceClass <-
           ProfileKernelEventEvidenceClass(Profile),

         ALKClaims <- ProfileClaims(Profile),
         ALKSubjects <- ProfileSubjects,
         ALKStructures <- Structures,
         ALKExecutionModalities <- ExecutionModalities,
         ALKObligationOccurrences <- ObligationOccurrences,
         ALKObligations <- Obligations,
         ALKStructureObligationOccurrences <-
           StructureObligationOccurrences,
         ALKExecutionModalityObligationOccurrences <-
           ExecutionModalityObligationOccurrences,
         ALKNormalizedKeyOf <- NormalizedKeyOf,
         ALKSelectedStructures <-
           ProfileSelectedStructuresForClaim(Profile),
         ALKSelectedExecutionModality <-
           [claim \in ProfileClaims(Profile) |->
               ProfileSelectedExecutionModality(Profile)],
         ALKCompositionSeamObligationOccurrences <-
           ProfileCompositionSeamObligationOccurrences(Profile),
         ALKClaimObligationOccurrences <-
           ProfileClaimObligationOccurrences(Profile),
         ALKClaimObligations <- ProfileClaimObligations(Profile),
         ALKGuaranteeObligations <-
           ProfileGuaranteeObligations(Profile),
         ALKActionLabels <- ProfileActionLabels,
         ALKPotentialActions <- ProfilePotentialActions,
         ALKActors <- ProfileActors,
         ALKObligationPropertyClass <- ObligationPropertyClass,
         ALKObligationStates <- ProfileObligationStates,
         ALKViolationStates <- ProfileViolationStates,
         ALKAllowedRelationSteps <- ProfileAllowedRelationSteps,
         ALKViolatingActions <- ProfileViolatingActions,
         ALKDerivedFrom <- ProfileDerivedFrom,
         ALKLivenessActiveStates <- ProfileLivenessActiveStates,
         ALKLivenessClosedStates <- ProfileLivenessClosedStates,
         ALKLivenessProgressActions <- ProfileLivenessProgressActions,
         ALKLivenessOtherActions <- ProfileLivenessOtherActions,
         ALKLivenessWeakFairProgressActions <-
           ProfileLivenessWeakFairProgressActions,
         ALKLivenessRankBound <- ProfileLivenessRankBound,
         ALKLivenessRank <- ProfileLivenessRank,
         ALKLivenessFairnessOwner <-
           ProfileLivenessFairnessOwner(Profile),
         ALKLivenessFairnessOwnerOf <-
           ProfileLivenessFairnessOwnerOf(Profile),
         ALKClaimActions <- ProfileClaimActions(Profile),
         ALKAdmittedActions <- ProfileAdmittedActions(Profile),
         ALKObligationRelevantActions <-
           ProfileObligationRelevantActions(Profile),
         ALKPathClassOf <- ProfilePathClassOf(Profile),
         ALKClaimCommitActions <- ProfileClaimCommitActions(Profile),
         ALKGovernedActions <- ProfileGovernedActions(Profile),
         ALKOwnerOf <- ProfileOwnerOf(Profile),
         ALKDelegateOf <- ProfileDelegateOf,
         ALKAuthority <- ProfileALKAuthority(Profile),
         ALKPostMediationSteps <- ProfilePostMediationSteps(Profile),
         ALKFormalStepsForClaim <- ProfileFormalStepsForClaim(Profile),
         ALKProviders <- ProfileProviders,
         ALKGuaranteeClaimant <- ProfileGuaranteeClaimant(Profile),
         ALKAssuranceProviderOf <- ProfileAssuranceProviderOf,
         ALKAssurancePositionOf <- ProfileAssurancePositionOf,
         ALKPreventionControllers <- ProfilePreventionControllers,
         ALKUnavailableProviders <- ProfileUnavailableProviders,
         ALKPersistentEvidenceFor <- ProfilePersistentEvidenceFor,
         ALKRecoveryAvailableFor <- ProfileRecoveryAvailableFor,
         ALKEvidenceEvents <- ProfileEvidenceEvents(Profile),
         ALKEvidenceRequiredActions <-
           ProfileEvidenceRequiredActions(Profile),
         ALKEvidenceForCommit <- ProfileEvidenceForCommit(Profile),
         ALKClaimSubject <- ProfileClaimSubject(Profile),
         ALKEvidenceKernelEvent <- ProfileEvidenceKernelEvent(Profile),
         ALKEventObservation <- ProfileEventObservation(Profile),
         ALKEventSubject <- ProfileEventSubject(Profile),
         ALKEventAction <- ProfileEventAction(Profile),
         ALKEventClaimant <- ProfileEventClaimant(Profile),
         ALKEventOwner <- ProfileEventOwner(Profile),
         ALKEventCommit <- ProfileEventCommit(Profile),
         ALKEventAssurance <- ProfileEventAssurance(Profile),
         ALKEventEvidenceClass <- ProfileEventEvidenceClass(Profile),
         ALKEvidenceProducer <- ProfileEvidenceProducer(Profile),
         ALKCustodianOf <- ProfileCustodianOf(Profile),
         ALKRetentionProviderOf <- ProfileRetentionProviderOf(Profile),
         ALKComponents <- ProfileComponents,
         ALKRelyEdges <- ProfileRelyEdges(Profile),
         ALKRelyRank <- ProfileRelyRank(Profile),
         ALKRelyPropertyClassOf <- ProfileRelyPropertyClassOf(Profile),
         ALKDirectMutualClosureEdges <-
           ProfileDirectMutualClosureEdges(Profile),
         ALKComponentObligationStates <-
           ProfileComponentObligationStates,
         ALKComponentRelySteps <- ProfileComponentRelySteps(Profile),
         ALKComponentGuaranteeSteps <-
           ProfileComponentGuaranteeSteps(Profile),
         ALKSharedStepsForRelyEdge <-
           ProfileSharedStepsForRelyEdge(Profile),
         ALKRepresentedSharedSteps <-
           ProfileRepresentedSharedSteps(Profile),
         ALKRegisteredSharedSteps <-
           ProfileRegisteredSharedSteps(Profile),
         ALKAffectedComponents <- ProfileAffectedComponents,
         ALKDependencies <- Dependencies,
         ALKClaimTCB <- ProfileClaimTCB(Profile),
         ALKActorDependency <- ProfileActorDependency,
         ALKProviderDependency <- ProfileProviderDependency,
         ALKBypassAbsent <- TRUE,
         ALKPartitionTolerated <- TRUE,
         ALKEpochCurrent <- TRUE,
         ALKAssuranceHealthyNow <- TRUE,
         ALKAuditPersistent <- TRUE,
         ALKExternalOwnerHealthy <- TRUE,
         ALKRetryAvailable <- TRUE,
         ALKRecoveryAvailableNow <- TRUE,
         ALKRequiredDependenciesBefore <-
           ProfileRequiredDependenciesBefore(Profile),
         ALKAddedRequiredDependencies <- {"future-adapter"},
         progressState <- progressState

ProfileInstantiatedPremises ==
    ProfileTheorem!ALKConstructionPremises

ProfileInstantiatedConclusion ==
    ProfileTheorem!ALKConstructionConclusion

InstantiatedProfileName == Profile

THEOREM AcceptedProfileConstructionTheorem ==
    ProfileInstantiatedPremises => ProfileInstantiatedConclusion
BY ProfileTheorem!ClaimRelativeALKConstruction
   DEF ProfileInstantiatedPremises, ProfileInstantiatedConclusion

====
