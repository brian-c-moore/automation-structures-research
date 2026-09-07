---- MODULE ALKConstructionTheorem_Proof ----
EXTENDS ALKConstructionTheorem, ALKRetainedRegistryData,
        ConstructionKernel_Proof, TLAPS

CONSTANTS ALKClaims, ALKSubjects, ALKStructures, ALKExecutionModalities,
          ALKObligationOccurrences, ALKObligations,
          ALKStructureObligationOccurrences,
          ALKExecutionModalityObligationOccurrences,
          ALKNormalizedKeyOf,
          ALKSelectedStructures, ALKSelectedExecutionModality,
          ALKCompositionSeamObligationOccurrences,
          ALKClaimObligationOccurrences, ALKClaimObligations,
          ALKGuaranteeObligations,
          ALKActionLabels, ALKPotentialActions, ALKActors,
          ALKObligationPropertyClass,
          ALKObligationStates, ALKViolationStates,
          ALKAllowedRelationSteps, ALKViolatingActions,
          ALKDerivedFrom,
          ALKLivenessActiveStates, ALKLivenessClosedStates,
          ALKLivenessProgressActions, ALKLivenessOtherActions,
          ALKLivenessWeakFairProgressActions,
          ALKLivenessRankBound, ALKLivenessRank,
          ALKLivenessFairnessOwner, ALKLivenessFairnessOwnerOf,
          ALKClaimActions, ALKAdmittedActions,
          ALKObligationRelevantActions, ALKPathClassOf,
          ALKClaimCommitActions, ALKGovernedActions,
          ALKOwnerOf, ALKDelegateOf, ALKAuthority,
          ALKPostMediationSteps, ALKFormalStepsForClaim,
          ALKProviders, ALKGuaranteeClaimant,
          ALKAssuranceProviderOf, ALKAssurancePositionOf,
          ALKPreventionControllers, ALKUnavailableProviders,
          ALKPersistentEvidenceFor, ALKRecoveryAvailableFor,
          ALKEvidenceEvents, ALKEvidenceRequiredActions,
          ALKEvidenceForCommit, ALKClaimSubject,
          ALKEvidenceKernelEvent,
          ALKEventObservation,
          ALKEventSubject, ALKEventAction, ALKEventClaimant,
          ALKEventOwner, ALKEventCommit, ALKEventAssurance,
          ALKEventEvidenceClass,
          ALKEvidenceProducer, ALKCustodianOf,
          ALKRetentionProviderOf,
          ALKComponents, ALKRelyEdges, ALKRelyRank,
          ALKRelyPropertyClassOf, ALKDirectMutualClosureEdges,
          ALKComponentObligationStates,
          ALKComponentRelySteps, ALKComponentGuaranteeSteps,
          ALKSharedStepsForRelyEdge,
          ALKRepresentedSharedSteps, ALKRegisteredSharedSteps,
          ALKAffectedComponents,
          ALKDependencies, ALKClaimTCB, ALKActorDependency,
          ALKProviderDependency,
          ALKBypassAbsent, ALKPartitionTolerated, ALKEpochCurrent,
          ALKAssuranceHealthyNow, ALKAuditPersistent,
          ALKExternalOwnerHealthy, ALKRetryAvailable,
          ALKRecoveryAvailableNow,
          ALKRequiredDependenciesBefore, ALKAddedRequiredDependencies

ALKExactSelectionAndObligationBoundary ==
    /\ ExactRetainedObligationRegistryBinding(
           ALKStructures, ALKExecutionModalities,
           ALKObligationOccurrences, ALKObligations,
           ALKStructureObligationOccurrences,
           ALKExecutionModalityObligationOccurrences,
           ALKNormalizedKeyOf, ALKObligationPropertyClass,
           RegistryStructureNames, RegistryExecutionModalityNames,
           RegistryObligationOccurrenceNames,
           RegistryNormalizedObligationNames,
           RegistryCarrierObligationOccurrences,
           RegistryNormalizedKeyOf,
           RegistryObligationPropertyClassOf)
    /\ ALKConstructionSelectionTyped(
           ALKClaims, ALKStructures, ALKExecutionModalities,
           ALKObligationOccurrences, ALKObligations,
           ALKStructureObligationOccurrences,
           ALKExecutionModalityObligationOccurrences,
           ALKNormalizedKeyOf,
           ALKSelectedStructures, ALKSelectedExecutionModality,
           ALKCompositionSeamObligationOccurrences,
           ALKClaimObligationOccurrences, ALKClaimObligations)
    /\ SelectedObligationBoundaryTyped(
           ObligationStateDomain, ALKActionLabels,
           ALKPotentialActions, ALKClaims, ALKObligations, ALKActors,
           ALKObligationPropertyClass,
           ALKClaimObligations, ALKObligationStates,
           ALKViolationStates, ALKAllowedRelationSteps,
           ALKViolatingActions, ALKDerivedFrom,
           ALKLivenessActiveStates, ALKLivenessClosedStates,
           ALKLivenessProgressActions, ALKLivenessOtherActions,
           ALKLivenessWeakFairProgressActions,
           ALKLivenessRankBound, ALKLivenessRank,
           ALKLivenessFairnessOwner, ALKLivenessFairnessOwnerOf)

ALKMediationPremises ==
    GovernedCommitMediationPremises(
        ObligationStateDomain, ALKClaims, ALKObligations,
        ALKActionLabels, ALKPotentialActions, ALKActors,
        ALKClaimActions, ALKAdmittedActions,
        ALKClaimObligations, ALKObligationPropertyClass,
        ALKViolatingActions, ALKLivenessProgressActions,
        ALKObligationRelevantActions, ALKPathClassOf,
        FormalCommitSteps, ALKClaimCommitActions,
        ALKGovernedActions, ALKOwnerOf, ALKAuthority)

ALKMediationConclusion ==
    GovernedCommitMediationConclusion(
        ALKClaims, ALKClaimActions, ALKObligationRelevantActions,
        ALKGovernedActions, ALKPathClassOf)

ALKMediationEnforcement ==
    MediationEnforcementPremises(
        ObligationStateDomain, ALKClaims, ALKObligations,
        ALKActionLabels, ALKAdmittedActions, ALKGovernedActions,
        ALKClaimObligations, ALKObligationStates,
        ALKPostMediationSteps, ALKFormalStepsForClaim)

ALKLivenessKernelBinding ==
    ExactLivenessKernelBinding(
        ALKClaims, ALKObligations, ALKActionLabels,
        ALKPotentialActions, ALKActors,
        ALKClaimObligations, ALKObligationPropertyClass,
        ALKLivenessClosedStates, ALKLivenessProgressActions,
        ALKLivenessOtherActions, ALKLivenessRankBound,
        ALKLivenessRank, ALKLivenessFairnessOwner,
        ALKLivenessFairnessOwnerOf,
        SelectedFamilies,
        ProgressClosedStates, DecreasingSteps, NonprogressSteps,
        ProgressRankBound, ProgressRank,
        ProgressFairnessOwner, ProgressFairnessOwnerOf)

ALKCommitAssuranceInventory ==
    CommitAssuranceInventoryTyped(
        ALKClaims, ALKActionLabels, ALKActors, ALKProviders,
        ALKClaimCommitActions, ALKGuaranteeClaimant, ALKOwnerOf,
        ALKAssuranceProviderOf, ALKAssurancePositionOf,
        ALKPreventionControllers, ALKUnavailableProviders,
        ALKPersistentEvidenceFor, ALKRecoveryAvailableFor)

ALKResultBundleForClaim(claim) ==
    ResultingClaimGuaranteeBundle(
        claim, RegisteredGuarantees, GuaranteeKindOf,
        ALKClaimCommitActions, ALKGuaranteeClaimant, ALKOwnerOf,
        ALKAssuranceProviderOf, ALKAssurancePositionOf,
        ALKPreventionControllers, ALKUnavailableProviders,
        ALKPersistentEvidenceFor, ALKRecoveryAvailableFor)

ALKWeakestCeilingForClaim(claim) ==
    WeakestGovernedCommitCeiling(
        claim, ALKClaimCommitActions,
        ALKGuaranteeClaimant, ALKOwnerOf,
        ALKAssuranceProviderOf, ALKAssurancePositionOf,
        ALKPreventionControllers, ALKUnavailableProviders,
        ALKPersistentEvidenceFor, ALKRecoveryAvailableFor)

ALKWeakestGuaranteeConclusion ==
    \A claim \in ALKClaims :
        /\ ALKResultBundleForClaim(claim)
             \subseteq SelectedKernelGuaranteeKinds(
                            RegisteredGuarantees, GuaranteeKindOf)
        /\ ALKResultBundleForClaim(claim)
             \subseteq ALKWeakestCeilingForClaim(claim)

ALKCommitEvidencePremises ==
    OwnedCommitEvidencePremises(
        ObligationStateDomain, KernelCheckActMode,
        KernelCheckResultStates, KernelPredicateStates,
        KernelInterferenceSteps, KernelGovernedCommitSteps,
        ALKClaims, ALKSubjects, ALKActionLabels,
        ALKActors, ALKProviders,
        ALKEvidenceEvents, ALKClaimCommitActions,
        ALKEvidenceRequiredActions, ALKEvidenceForCommit,
        ALKClaimSubject, ALKGuaranteeClaimant, ALKOwnerOf,
        ALKAssurancePositionOf,
        ALKEventSubject, ALKEventAction, ALKEventClaimant,
        ALKEventOwner, ALKEventCommit, ALKEventAssurance,
        ALKEvidenceProducer, ALKCustodianOf,
        ALKRetentionProviderOf)

ALKEvidenceRequirementBinding ==
    ExactEvidenceRequirementBinding(
        ALKClaims, ALKActionLabels,
        RegisteredGuarantees, GuaranteeKindOf,
        GuaranteePropertyClass,
        ALKClaimCommitActions, ALKEvidenceRequiredActions)

ALKCommitEvidenceConclusion ==
    OwnedCommitEvidenceConclusion(
        ObligationStateDomain, KernelPredicateStates,
        KernelGovernedCommitSteps,
        ALKClaims, ALKEvidenceRequiredActions,
        ALKEvidenceForCommit, ALKEventAssurance)

ALKProviderBackedRelyPremises ==
    ProviderBackedRelyPremises(
        ObligationStateDomain, ALKComponents,
        ALKRelyEdges, ALKRelyRank, ALKRelyPropertyClassOf,
        ALKDirectMutualClosureEdges,
         ALKComponentObligationStates,
         ALKComponentRelySteps, ALKComponentGuaranteeSteps,
         ALKSharedStepsForRelyEdge, ALKRegisteredSharedSteps)

ALKProviderBackedRelyConclusion ==
    ProviderBackedRelyConclusion(
        ALKComponents, ALKRelyEdges, ALKRelyRank,
        ALKRelyPropertyClassOf, ALKDirectMutualClosureEdges,
        ALKComponentRelySteps, ALKComponentGuaranteeSteps)

ALKSharedTransitionPremises ==
    SharedTransitionPremises(
        ObligationStateDomain, ALKComponents,
        ALKRepresentedSharedSteps, ALKRegisteredSharedSteps,
        ALKAffectedComponents, ALKComponentObligationStates)

ALKSharedTransitionConclusion ==
    SharedTransitionPreservation(
        ObligationStateDomain, ALKRegisteredSharedSteps,
        ALKAffectedComponents, ALKComponentObligationStates)

ALKFailureInputs ==
    FailureInputsTyped(
        ALKBypassAbsent, ALKPartitionTolerated, ALKEpochCurrent,
        ALKAssuranceHealthyNow, ALKAuditPersistent,
        ALKExternalOwnerHealthy, ALKRetryAvailable,
        ALKRecoveryAvailableNow)

ALKBypassFailureInputBinding ==
    ExactBypassFailureInputBinding(
        ALKClaims, ALKActionLabels, ALKPotentialActions,
        ALKClaimActions, ALKPathClassOf, ALKBypassAbsent)

ALKFailureNarrowingConclusion ==
    \A claim \in ALKClaims :
        NamedFailureNarrowingConclusion(
            ALKResultBundleForClaim(claim),
            ALKBypassAbsent, ALKPartitionTolerated, ALKEpochCurrent,
            ALKAssuranceHealthyNow, ALKAuditPersistent,
            ALKExternalOwnerHealthy, ALKRetryAvailable,
            ALKRecoveryAvailableNow)

ALKTCBClosure ==
    ExactClaimTCBClosure(
        ALKClaims, ALKObligations, ALKActionLabels,
        ALKActors, ALKProviders, ALKEvidenceEvents,
        ALKDependencies, ALKClaimTCB,
        ALKClaimObligations, ALKObligationPropertyClass,
        ALKLivenessFairnessOwner,
        ALKGuaranteeClaimant, ALKAuthority,
        ALKAdmittedActions, ALKClaimCommitActions,
        ALKOwnerOf, ALKDelegateOf, ALKAssuranceProviderOf,
        ALKActorDependency, ALKEvidenceForCommit,
        ALKEvidenceProducer, ALKCustodianOf, ALKRetentionProviderOf,
        ALKProviderDependency)

ALKTCBInputGrowth ==
    ExactTCBRequirementGrowthBinding(
        ALKClaims, ALKDependencies,
        ALKClaimObligations, ALKObligationPropertyClass,
        ALKLivenessFairnessOwner,
        ALKGuaranteeClaimant, ALKAuthority,
        ALKAdmittedActions, ALKClaimCommitActions,
        ALKOwnerOf, ALKDelegateOf, ALKAssuranceProviderOf,
        ALKActorDependency, ALKEvidenceForCommit,
        ALKEvidenceProducer, ALKCustodianOf,
        ALKRetentionProviderOf, ALKProviderDependency,
        ALKRequiredDependenciesBefore,
        ALKAddedRequiredDependencies)

ALKTCBMonotonicityConclusion ==
    FixedClaimTCBMonotonicity(
        ALKDependencies, ALKRequiredDependenciesBefore,
        ALKAddedRequiredDependencies)

ALKKernelBoundaryReuse ==
    /\ "check-act" \in SelectedFamilies
    /\ "composition" \in SelectedFamilies
    /\ KernelGovernedCommitSteps = FormalCommitSteps
    /\ \A claim \in ALKClaims :
          ALKFormalStepsForClaim[claim] = FormalSteps
    /\ KernelSelectionGuaranteeBinding(
           ALKClaims, ALKStructures, ALKExecutionModalities,
           ALKObligations, ObligationStateDomain,
           ALKSelectedStructures, ALKSelectedExecutionModality,
           ALKClaimObligations, ALKObligationPropertyClass,
           ALKObligationStates,
           SelectedStructures, SelectedExecutionCarrier,
           RegisteredGuarantees, GuaranteeFamily,
           GuaranteePropertyClass, ALKGuaranteeObligations,
           RegisteredObligationStates)
    /\ KernelCommitAssuranceBinding(
           ALKClaims, ALKActionLabels, ALKPotentialActions,
           ALKPostMediationSteps,
           ALKClaimCommitActions, ALKGuaranteeClaimant,
           ALKOwnerOf, ALKDelegateOf,
           ALKAssuranceProviderOf, ALKAssurancePositionOf,
           ALKPreventionControllers, ALKUnavailableProviders,
           ALKPersistentEvidenceFor, ALKRecoveryAvailableFor,
           FormalCommitSteps, FormalCommitOwner, FormalCommitDelegate,
           FormalCommitAssurance,
           AssuranceClaimant, KernelAssuranceProvider,
           KernelPreventionControllers, AssuranceUnavailableProviders,
           KernelPersistentEvidence, KernelRecoveryAvailable)
    /\ KernelCompositionBinding(
           ALKComponents, ALKRelyEdges,
           ALKComponentObligationStates,
           ALKComponentRelySteps, ALKComponentGuaranteeSteps,
           ALKRegisteredSharedSteps,
           CompositionRelyEdges, CompositionInvA, CompositionInvB,
           CompositionRelyA, CompositionRelyB,
           CompositionStepA, CompositionStepB,
           CompositionSharedSteps)
    /\ KernelEvidenceBinding(
           ALKClaims, ALKEvidenceEvents, EvidenceEvents,
           ALKEvidenceRequiredActions, ALKEvidenceForCommit,
           FormalCommitSteps,
           ALKEvidenceKernelEvent,
           ALKEventObservation,
           ALKEventSubject, ALKEventAction,
           ALKEventClaimant, ALKEventOwner,
           ALKEventCommit, ALKEventAssurance,
           ALKEventEvidenceClass,
           ALKPostMediationSteps,
           EventObservation,
           EventSubject, EventAction, EventClaimant, EventOwner,
           EventCommit, EventAssurance, EventEvidenceClass)

ALKConstructionPremises ==
    /\ ConstructionFamilyPremises
    /\ ALKExactSelectionAndObligationBoundary
    /\ ALKMediationPremises
    /\ ALKMediationEnforcement
    /\ ALKLivenessKernelBinding
    /\ ALKCommitAssuranceInventory
    /\ ALKEvidenceRequirementBinding
    /\ ALKCommitEvidencePremises
    /\ ALKProviderBackedRelyPremises
    /\ ALKSharedTransitionPremises
    /\ ALKFailureInputs
    /\ ALKBypassFailureInputBinding
    /\ ALKTCBClosure
    /\ ALKTCBInputGrowth
    /\ ALKKernelBoundaryReuse

ALKConstructionConclusion ==
    /\ ConstructionFamilyConclusion
    /\ ALKMediationConclusion
    /\ ALKWeakestGuaranteeConclusion
    /\ ALKCommitEvidenceConclusion
    /\ ALKProviderBackedRelyConclusion
    /\ ALKSharedTransitionConclusion
    /\ ALKFailureNarrowingConclusion
    /\ ALKTCBMonotonicityConclusion

LEMMA MediationCompletenessOverGovernedActions ==
    ALKMediationPremises => ALKMediationConclusion
BY SMT DEF ALKMediationPremises, ALKMediationConclusion,
           GovernedCommitMediationPremises,
           GovernedCommitMediationConclusion,
           ExactGovernedActionBoundary, ExactClaimPathInventory,
           DerivedGovernedActionsFor,
           MediationBoundaryTyped,
           CompleteMediation, MediatedActionsFor

LEMMA NoStrongerGuaranteeThanWeakestCommit ==
    ALKCommitAssuranceInventory => ALKWeakestGuaranteeConclusion
BY SMT DEF ALKCommitAssuranceInventory,
           ALKWeakestGuaranteeConclusion,
           ALKResultBundleForClaim, ALKWeakestCeilingForClaim,
           ResultingClaimGuaranteeBundle

LEMMA CheckActEvidenceCouplingAtOwnedCommits ==
    /\ ConstructionFamilyPremises
    /\ "check-act" \in SelectedFamilies
    /\ ALKCommitEvidencePremises
    => ALKCommitEvidenceConclusion
PROOF
  <1> SUFFICES ASSUME
        /\ ConstructionFamilyPremises
        /\ "check-act" \in SelectedFamilies
        /\ ALKCommitEvidencePremises
      PROVE ALKCommitEvidenceConclusion
    OBVIOUS
  <1>check_premises. CheckActFamilyPremises
    BY
       DEF ConstructionFamilyPremises, ConstructionAdmitted,
           ApplicableKernelClaims
  <1>check_conclusion. CheckActFamilyConclusion
    BY <1>check_premises, CheckActStability
       DEF CheckActFamilyPremises, CheckActFamilyConclusion
  <1>evidence. \A claim \in ALKClaims :
           AtomicCommitEvidenceCoupled(
               ALKEvidenceRequiredActions[claim],
               ALKEvidenceForCommit, ALKEventAssurance)
    <2> SUFFICES ASSUME NEW claim \in ALKClaims
        PROVE AtomicCommitEvidenceCoupled(
                  ALKEvidenceRequiredActions[claim],
                  ALKEvidenceForCommit, ALKEventAssurance)
      OBVIOUS
    <2>domain. ALKEvidenceRequiredActions[claim]
          \subseteq DOMAIN ALKEvidenceForCommit
      BY SMT DEF ALKCommitEvidencePremises,
                 OwnedCommitEvidencePremises,
                 ExactCommitEvidencePremises
    <2>events. \A action \in ALKEvidenceRequiredActions[claim] :
          /\ ALKEvidenceForCommit[action] # {}
          /\ \A event \in ALKEvidenceForCommit[action] :
                ALKEventAssurance[event] = "at-commit"
      <3> SUFFICES ASSUME
            NEW action \in ALKEvidenceRequiredActions[claim]
          PROVE /\ ALKEvidenceForCommit[action] # {}
                /\ \A event \in ALKEvidenceForCommit[action] :
                      ALKEventAssurance[event] = "at-commit"
        OBVIOUS
      <3>commit_member. action \in ALKClaimCommitActions[claim]
        BY SMT DEF ALKCommitEvidencePremises,
                   OwnedCommitEvidencePremises,
                   ExactCommitEvidencePremises
      <3>nonempty. ALKEvidenceForCommit[action] # {}
        BY <3>commit_member
           DEF ALKCommitEvidencePremises,
                   OwnedCommitEvidencePremises,
                   ExactCommitEvidencePremises
      <3>position. ALKAssurancePositionOf[action] = "at-commit"
        BY SMT DEF ALKCommitEvidencePremises,
                   OwnedCommitEvidencePremises
      <3>binding. \A event \in ALKEvidenceForCommit[action] :
            ALKEventAssurance[event] =
              ALKAssurancePositionOf[action]
        BY <3>commit_member
           DEF ALKCommitEvidencePremises,
                   OwnedCommitEvidencePremises,
                   ExactCommitEvidencePremises
      <3> QED BY <3>nonempty, <3>position, <3>binding
    <2> QED BY <2>domain, <2>events
         DEF AtomicCommitEvidenceCoupled
  <1> QED BY <1>check_conclusion, <1>evidence
       DEF ALKCommitEvidenceConclusion,
           OwnedCommitEvidenceConclusion,
           CheckActFamilyConclusion

LEMMA ProviderBackedReliesWithoutCircularCredit ==
    ALKProviderBackedRelyPremises => ALKProviderBackedRelyConclusion
BY DEF ALKProviderBackedRelyPremises,
       ALKProviderBackedRelyConclusion,
       ProviderBackedRelyPremises, ProviderBackedRelyConclusion,
       RelyDischargeBoundaryTyped

LEMMA InternalSharedTransitionsPreserveAffectedObligations ==
    ALKSharedTransitionPremises => ALKSharedTransitionConclusion
BY DEF ALKSharedTransitionPremises, ALKSharedTransitionConclusion,
       SharedTransitionPremises

LEMMA NamedFailuresOnlyNarrowTheDerivedBundle ==
    /\ ConstructionFamilyPremises
    /\ ALKCommitAssuranceInventory
    /\ ALKFailureInputs
    => ALKFailureNarrowingConclusion
PROOF
  <1> SUFFICES ASSUME
        /\ ConstructionFamilyPremises
        /\ ALKCommitAssuranceInventory
        /\ ALKFailureInputs
      PROVE ALKFailureNarrowingConclusion
    OBVIOUS
  <1>registered_kinds.
      SelectedKernelGuaranteeKinds(
          RegisteredGuarantees, GuaranteeKindOf)
        \subseteq GuaranteeKinds
    BY SMT DEF ConstructionFamilyPremises, ConstructionAdmitted,
               ConstructionStaticAdmission, GuaranteeBundleTyped,
               SelectedKernelGuaranteeKinds
  <1>normal_typed. \A claim \in ALKClaims :
        ALKResultBundleForClaim(claim) \subseteq GuaranteeKinds
    BY <1>registered_kinds,
       NoStrongerGuaranteeThanWeakestCommit
       DEF ALKWeakestGuaranteeConclusion
  <1> QED BY SMT, <1>normal_typed
       DEF ALKFailureInputs, ALKFailureNarrowingConclusion,
           FailureInputsTyped,
           NamedFailureNarrowingConclusion,
           DerivedFailureGuaranteeBundle,
           DerivedFailureCeiling,
           ALKFailureClasses, GuaranteeKinds

LEMMA FixedClaimTCBRequirementMonotonicity ==
    ALKTCBInputGrowth => ALKTCBMonotonicityConclusion
BY SMT DEF ALKTCBInputGrowth, ALKTCBMonotonicityConclusion,
           ExactTCBRequirementGrowthBinding,
           FixedClaimTCBMonotonicity, SufficientTCBs

THEOREM ClaimRelativeALKConstruction ==
    ALKConstructionPremises => ALKConstructionConclusion
PROOF
  <1> SUFFICES ASSUME ALKConstructionPremises
      PROVE ALKConstructionConclusion
    OBVIOUS
  <1>kernel. ConstructionFamilyConclusion
    BY BoundedConstructionSufficiency
       DEF ALKConstructionPremises
  <1>mediation. ALKMediationConclusion
    BY MediationCompletenessOverGovernedActions
       DEF ALKConstructionPremises
  <1>weakest. ALKWeakestGuaranteeConclusion
    BY NoStrongerGuaranteeThanWeakestCommit
       DEF ALKConstructionPremises
  <1>evidence. ALKCommitEvidenceConclusion
    BY CheckActEvidenceCouplingAtOwnedCommits
       DEF ALKConstructionPremises, ALKKernelBoundaryReuse
  <1>relies. ALKProviderBackedRelyConclusion
    BY ProviderBackedReliesWithoutCircularCredit
       DEF ALKConstructionPremises
  <1>shared. ALKSharedTransitionConclusion
    BY InternalSharedTransitionsPreserveAffectedObligations
       DEF ALKConstructionPremises
  <1>failures. ALKFailureNarrowingConclusion
    BY NamedFailuresOnlyNarrowTheDerivedBundle
       DEF ALKConstructionPremises
  <1>tcb. ALKTCBMonotonicityConclusion
    BY FixedClaimTCBRequirementMonotonicity
       DEF ALKConstructionPremises
  <1> QED BY <1>kernel, <1>mediation, <1>weakest,
                  <1>evidence, <1>relies, <1>shared,
                  <1>failures, <1>tcb
       DEF ALKConstructionConclusion

====
