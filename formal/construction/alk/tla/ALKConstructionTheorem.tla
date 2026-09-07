---- MODULE ALKConstructionTheorem ----
EXTENDS ALKSemanticModel, ConstructionKernel

ExactRetainedObligationRegistryBinding(
        Structures, ExecutionModalities,
        ObligationOccurrences, Obligations,
        StructureObligationOccurrences,
        ExecutionModalityObligationOccurrences,
        NormalizedKeyOf, ObligationPropertyClass,
        RegisteredStructures, RegisteredExecutionModalities,
        RegisteredObligationOccurrences, RegisteredObligations,
        RegisteredCarrierObligationOccurrences,
        RegisteredNormalizedKeyOf,
        RegisteredObligationPropertyClassOf) ==
    /\ Structures = RegisteredStructures
    /\ ExecutionModalities = RegisteredExecutionModalities
    /\ ObligationOccurrences = RegisteredObligationOccurrences
    /\ Obligations = RegisteredObligations
    /\ StructureObligationOccurrences =
         [structure \in RegisteredStructures |->
             RegisteredCarrierObligationOccurrences[structure]]
    /\ ExecutionModalityObligationOccurrences =
         [modality \in RegisteredExecutionModalities |->
             RegisteredCarrierObligationOccurrences[modality]]
    /\ NormalizedKeyOf = RegisteredNormalizedKeyOf
    /\ ObligationPropertyClass =
         [obligation \in RegisteredObligations |->
             RegisteredObligationPropertyClassOf[obligation]]

RepresentedCommitActionsFor(ActionLabels, Actions, GovernedCommitSteps) ==
    {action \in ActionLabels :
        Actions[action] \cap GovernedCommitSteps # {}}

DerivedGovernedActionsFor(
        claim, ClaimObligations, ObligationPropertyClass,
        ViolatingActions, LivenessProgressActions,
        ClaimCommitActions, AdmittedActions) ==
    AdmittedActions[claim]
      \cap (SelectedGovernanceActionsFor(
               claim, ClaimObligations, ObligationPropertyClass,
               ViolatingActions, LivenessProgressActions)
             \cup ClaimCommitActions[claim])

ExactClaimPathInventory(Claims, ActionLabels, ClaimActions) ==
    /\ ClaimActions \in [Claims -> SUBSET ActionLabels]
    /\ \A claim \in Claims : ClaimActions[claim] = ActionLabels

ExactGovernedActionBoundary(
        S, Claims, Obligations, ActionLabels, Actions,
        ClaimActions, AdmittedActions,
        ClaimObligations, ObligationPropertyClass,
        ViolatingActions, LivenessProgressActions,
        GovernedCommitSteps, ClaimCommitActions,
        GovernedActions) ==
    /\ ActionFamilyTyped(S, ActionLabels, Actions)
    /\ ExactClaimPathInventory(Claims, ActionLabels, ClaimActions)
    /\ RelationTyped(S, GovernedCommitSteps)
    /\ GovernedCommitSteps # {}
    /\ ClaimCommitActions \in [Claims -> SUBSET ActionLabels]
    /\ GovernedActions \in [Claims -> SUBSET ActionLabels]
    /\ \A claim \in Claims :
          /\ ClaimCommitActions[claim] =
               RepresentedCommitActionsFor(
                   ActionLabels, Actions, GovernedCommitSteps)
          /\ GovernedCommitSteps =
               UNION {
                   Actions[action] \cap GovernedCommitSteps :
                   action \in ClaimCommitActions[claim]}
          /\ GovernedActions[claim] =
               DerivedGovernedActionsFor(
                   claim, ClaimObligations, ObligationPropertyClass,
                   ViolatingActions, LivenessProgressActions,
                   ClaimCommitActions, AdmittedActions)

GovernedCommitMediationPremises(
        S, Claims, Obligations, ActionLabels, Actions, Actors,
        ClaimActions, AdmittedActions,
        ClaimObligations, ObligationPropertyClass,
        ViolatingActions, LivenessProgressActions,
        ObligationRelevantActions, PathClassOf,
        GovernedCommitSteps, ClaimCommitActions,
        GovernedActions, OwnerOf, ALKAuthority) ==
    /\ MediationBoundaryTyped(
           S, Claims, Obligations, ActionLabels, Actions,
           ClaimActions, AdmittedActions, ClaimObligations,
           ObligationPropertyClass, ViolatingActions,
           LivenessProgressActions,
           ObligationRelevantActions, PathClassOf)
    /\ ExactGovernedActionBoundary(
           S, Claims, Obligations, ActionLabels, Actions,
           ClaimActions, AdmittedActions,
           ClaimObligations, ObligationPropertyClass,
           ViolatingActions, LivenessProgressActions,
           GovernedCommitSteps, ClaimCommitActions,
           GovernedActions)
    /\ OwnerOf \in [ActionLabels -> Actors]
    /\ ALKAuthority \in [Claims -> SUBSET Actors]
    /\ \A claim \in Claims :
          /\ ObligationRelevantActions[claim] = GovernedActions[claim]
          /\ \A action \in GovernedActions[claim] :
                /\ PathClassOf[claim][action] = "mediated"
                /\ OwnerOf[action] \in ALKAuthority[claim]

GovernedCommitMediationConclusion(
        Claims, ClaimActions, ObligationRelevantActions,
        GovernedActions, PathClassOf) ==
    \A claim \in Claims :
        /\ ObligationRelevantActions[claim] = GovernedActions[claim]
        /\ CompleteMediation(
               claim, ClaimActions, ObligationRelevantActions,
               PathClassOf)

MediationEnforcementPremises(
        S, Claims, Obligations, ActionLabels,
        AdmittedActions, GovernedActions,
        ClaimObligations, ObligationStates,
        PostMediationSteps, FormalStepsForClaim) ==
    /\ AdmittedActions \in [Claims -> SUBSET ActionLabels]
    /\ GovernedActions \in [Claims -> SUBSET ActionLabels]
    /\ ClaimObligations \in [Claims -> SUBSET Obligations]
    /\ ObligationStates \in [Obligations -> SUBSET S]
    /\ PostMediationSteps \in [ActionLabels -> SUBSET Pairs(S)]
    /\ FormalStepsForClaim \in [Claims -> SUBSET Pairs(S)]
    /\ \A claim \in Claims :
          /\ FormalStepsForClaim[claim] =
               ActionUnion(AdmittedActions[claim], PostMediationSteps)
          /\ \A obligation \in ClaimObligations[claim] :
                /\ ObligationStates[obligation] # {}
                /\ \A action \in AdmittedActions[claim] :
                      Stable(
                          S, ObligationStates[obligation],
                          PostMediationSteps[action])

SelectedLivenessObligationsFor(
        claim, ClaimObligations, ObligationPropertyClass) ==
    {obligation \in ClaimObligations[claim] :
        ObligationPropertyClass[obligation] = "liveness"}

ExactLivenessKernelBinding(
        Claims, Obligations, ActionLabels, Actions, Actors,
        ClaimObligations, ObligationPropertyClass,
        LivenessClosedStates, LivenessProgressActions,
        LivenessOtherActions, LivenessRankBound, LivenessRank,
        LivenessFairnessOwner, LivenessFairnessOwnerOf,
        SelectedFamilies,
        FormalClosedStates, FormalProgressSteps, FormalOtherSteps,
        FormalRankBound, FormalRank,
        FormalFairnessOwner, FormalFairnessOwnerOf) ==
    /\ ClaimObligations \in [Claims -> SUBSET Obligations]
    /\ ObligationPropertyClass \in [Obligations -> PropertyClasses]
    /\ LivenessClosedStates \in [Obligations -> SUBSET DOMAIN FormalRank]
    /\ LivenessProgressActions
         \in [Obligations -> SUBSET ActionLabels]
    /\ LivenessOtherActions \in [Obligations -> SUBSET ActionLabels]
    /\ LivenessRankBound \in [Obligations -> Nat]
    /\ LivenessRank \in [Obligations -> [DOMAIN FormalRank -> Nat]]
    /\ LivenessFairnessOwner \in [Obligations -> Actors]
    /\ LivenessFairnessOwnerOf
         \in [Obligations -> [ActionLabels -> Actors]]
    /\ FormalFairnessOwnerOf
         \in [FormalProgressSteps -> Actors]
    /\ \A claim \in Claims :
          LET SelectedLiveness ==
                SelectedLivenessObligationsFor(
                    claim, ClaimObligations,
                    ObligationPropertyClass)
          IN SelectedLiveness # {}
               => /\ "progress" \in SelectedFamilies
                  /\ \A obligation \in SelectedLiveness :
                        /\ ActionUnion(
                               LivenessProgressActions[obligation],
                               Actions) = FormalProgressSteps
                        /\ ActionUnion(
                               LivenessOtherActions[obligation],
                               Actions) = FormalOtherSteps
                        /\ LivenessClosedStates[obligation] =
                             FormalClosedStates
                        /\ LivenessRankBound[obligation] = FormalRankBound
                        /\ LivenessRank[obligation] = FormalRank
                        /\ LivenessFairnessOwner[obligation] =
                             FormalFairnessOwner
                        /\ \A action \in
                                  LivenessProgressActions[obligation] :
                              LivenessFairnessOwnerOf[obligation][action] =
                                FormalFairnessOwner

CommitAssuranceInventoryTyped(
        Claims, ActionLabels, Actors, Providers,
        ClaimCommitActions, GuaranteeClaimant, OwnerOf,
        AssuranceProviderOf, AssurancePositionOf,
        PreventionControllers,
        UnavailableProviders, PersistentEvidenceFor,
        RecoveryAvailableFor) ==
    /\ ClaimCommitActions \in [Claims -> SUBSET ActionLabels]
    /\ GuaranteeClaimant \in [Claims -> Actors]
    /\ OwnerOf \in [ActionLabels -> Actors]
    /\ AssuranceProviderOf \in [ActionLabels -> Providers]
    /\ AssurancePositionOf \in [ActionLabels -> AssurancePositions]
    /\ PreventionControllers \subseteq Actors
    /\ UnavailableProviders \subseteq Providers
    /\ PersistentEvidenceFor \in [ActionLabels -> BOOLEAN]
    /\ RecoveryAvailableFor \in [ActionLabels -> BOOLEAN]
    /\ \A claim \in Claims : ClaimCommitActions[claim] # {}

CommitGuaranteeCeiling(
        claim, action, GuaranteeClaimant, OwnerOf,
        AssuranceProviderOf, AssurancePositionOf,
        PreventionControllers, UnavailableProviders,
        PersistentEvidenceFor, RecoveryAvailableFor) ==
    GuaranteeCeiling(
        GuaranteeClaimant[claim], OwnerOf[action],
        AssuranceProviderOf[action], AssurancePositionOf[action],
        PreventionControllers, UnavailableProviders,
        PersistentEvidenceFor[action], RecoveryAvailableFor[action])

\* GuaranteeClaimant is the relying party. Each action's OwnerOf value is
\* the single owner that issues the guarantee represented by this ceiling.
WeakestGovernedCommitCeiling(
        claim, ClaimCommitActions, GuaranteeClaimant, OwnerOf,
        AssuranceProviderOf, AssurancePositionOf,
        PreventionControllers, UnavailableProviders,
        PersistentEvidenceFor, RecoveryAvailableFor) ==
    {kind \in GuaranteeKinds :
        \A action \in ClaimCommitActions[claim] :
            kind \in CommitGuaranteeCeiling(
                       claim, action, GuaranteeClaimant, OwnerOf,
                       AssuranceProviderOf, AssurancePositionOf,
                       PreventionControllers, UnavailableProviders,
                       PersistentEvidenceFor, RecoveryAvailableFor)}

SelectedKernelGuaranteeKinds(RegisteredGuarantees, GuaranteeKindOf) ==
    {GuaranteeKindOf[guarantee] : guarantee \in RegisteredGuarantees}

ResultingClaimGuaranteeBundle(
        claim, RegisteredGuarantees, GuaranteeKindOf,
        ClaimCommitActions, GuaranteeClaimant, OwnerOf,
        AssuranceProviderOf, AssurancePositionOf,
        PreventionControllers, UnavailableProviders,
        PersistentEvidenceFor, RecoveryAvailableFor) ==
    SelectedKernelGuaranteeKinds(
        RegisteredGuarantees, GuaranteeKindOf)
      \cap WeakestGovernedCommitCeiling(
               claim, ClaimCommitActions, GuaranteeClaimant, OwnerOf,
               AssuranceProviderOf, AssurancePositionOf,
               PreventionControllers, UnavailableProviders,
               PersistentEvidenceFor, RecoveryAvailableFor)

ClaimGuaranteeBundleMatchesDerived(
        Claims, AdvertisedGuaranteeBundle,
        RegisteredGuarantees, GuaranteeKindOf,
        ClaimCommitActions, GuaranteeClaimant, OwnerOf,
        AssuranceProviderOf, AssurancePositionOf,
        PreventionControllers, UnavailableProviders,
        PersistentEvidenceFor, RecoveryAvailableFor) ==
    /\ AdvertisedGuaranteeBundle \in [Claims -> SUBSET GuaranteeKinds]
    /\ \A claim \in Claims :
          AdvertisedGuaranteeBundle[claim] =
            ResultingClaimGuaranteeBundle(
                claim, RegisteredGuarantees, GuaranteeKindOf,
                ClaimCommitActions, GuaranteeClaimant, OwnerOf,
                AssuranceProviderOf, AssurancePositionOf,
                PreventionControllers, UnavailableProviders,
                PersistentEvidenceFor, RecoveryAvailableFor)

EvidenceRequiredByRegistration(
        RegisteredGuarantees, GuaranteeKindOf,
        GuaranteePropertyClass) ==
    \/ \E guarantee \in RegisteredGuarantees :
          GuaranteePropertyClass[guarantee] = "evidence"
    \/ {GuaranteeKindOf[guarantee] :
            guarantee \in RegisteredGuarantees}
         \cap {"detection", "recovery"} # {}

ExactEvidenceRequirementBinding(
        Claims, ActionLabels,
        RegisteredGuarantees, GuaranteeKindOf,
        GuaranteePropertyClass,
        ClaimCommitActions, EvidenceRequiredActions) ==
    /\ GuaranteeKindOf \in [RegisteredGuarantees -> GuaranteeKinds]
    /\ GuaranteePropertyClass
         \in [RegisteredGuarantees -> KernelTracePropertyClasses]
    /\ ClaimCommitActions \in [Claims -> SUBSET ActionLabels]
    /\ EvidenceRequiredActions \in [Claims -> SUBSET ActionLabels]
    /\ \A claim \in Claims :
          EvidenceRequiredActions[claim] =
            IF EvidenceRequiredByRegistration(
                   RegisteredGuarantees, GuaranteeKindOf,
                   GuaranteePropertyClass)
              THEN ClaimCommitActions[claim]
              ELSE {}

ExactCommitEvidencePremises(
        Claims, Subjects, ActionLabels, Actors, Providers,
        EvidenceEvents, ClaimCommitActions, EvidenceRequiredActions,
        EvidenceForCommit, ClaimSubject, GuaranteeClaimant, OwnerOf,
        AssurancePositionOf,
        EventSubject, EventAction, EventClaimant, EventOwner,
        EventCommit, EventAssurance,
        EvidenceProducer, CustodianOf, RetentionProviderOf) ==
    LET AllCommitActions ==
          UNION {ClaimCommitActions[claim] : claim \in Claims}
    IN
    /\ ClaimCommitActions \in [Claims -> SUBSET ActionLabels]
    /\ EvidenceRequiredActions \in [Claims -> SUBSET ActionLabels]
    /\ EvidenceForCommit \in [AllCommitActions -> SUBSET EvidenceEvents]
    /\ ClaimSubject \in [Claims -> Subjects]
    /\ GuaranteeClaimant \in [Claims -> Actors]
    /\ OwnerOf \in [ActionLabels -> Actors]
    /\ AssurancePositionOf \in [ActionLabels -> AssurancePositions]
    /\ EventSubject \in [EvidenceEvents -> Subjects]
    /\ EventAction \in [EvidenceEvents -> ActionLabels]
    /\ EventClaimant \in [EvidenceEvents -> Actors]
    /\ EventOwner \in [EvidenceEvents -> Actors]
    /\ EventCommit \in [EvidenceEvents -> AllCommitActions]
    /\ EventAssurance \in [EvidenceEvents -> AssurancePositions]
    /\ EvidenceProducer \in [EvidenceEvents -> Actors]
    /\ CustodianOf \in [EvidenceEvents -> Actors]
    /\ RetentionProviderOf \in [EvidenceEvents -> Providers]
    /\ EvidenceEvents =
         UNION {EvidenceForCommit[action] : action \in AllCommitActions}
    /\ \A claim \in Claims :
          /\ EvidenceRequiredActions[claim]
               \subseteq ClaimCommitActions[claim]
          /\ \A action \in ClaimCommitActions[claim] :
                /\ action \in EvidenceRequiredActions[claim]
                     => EvidenceForCommit[action] # {}
                /\ \A event \in EvidenceForCommit[action] :
                      /\ EventSubject[event] = ClaimSubject[claim]
                      /\ EventAction[event] = action
                      /\ EventClaimant[event] = GuaranteeClaimant[claim]
                      /\ EventOwner[event] = OwnerOf[action]
                      /\ EventCommit[event] = action
                      /\ EventAssurance[event] =
                           AssurancePositionOf[action]

OwnedCommitEvidencePremises(
        S, CheckActMode, CheckResultStates, PredicateStates,
        InterferenceSteps, GovernedCommitSteps,
        Claims, Subjects, ActionLabels, Actors, Providers,
        EvidenceEvents, ClaimCommitActions, EvidenceRequiredActions,
        EvidenceForCommit, ClaimSubject, GuaranteeClaimant, OwnerOf,
        AssurancePositionOf,
        EventSubject, EventAction, EventClaimant, EventOwner,
        EventCommit, EventAssurance,
        EvidenceProducer, CustodianOf, RetentionProviderOf) ==
    /\ CheckActAdmission(
           S, CheckActMode, CheckResultStates, PredicateStates,
           InterferenceSteps, GovernedCommitSteps)
    /\ ExactCommitEvidencePremises(
           Claims, Subjects, ActionLabels, Actors, Providers,
           EvidenceEvents, ClaimCommitActions, EvidenceRequiredActions,
           EvidenceForCommit, ClaimSubject, GuaranteeClaimant, OwnerOf,
           AssurancePositionOf,
           EventSubject, EventAction, EventClaimant, EventOwner,
           EventCommit, EventAssurance,
           EvidenceProducer, CustodianOf, RetentionProviderOf)
    /\ \A claim \in Claims :
          \A action \in EvidenceRequiredActions[claim] :
              AssurancePositionOf[action] = "at-commit"

OwnedCommitEvidenceConclusion(
        S, PredicateStates, GovernedCommitSteps,
        Claims, EvidenceRequiredActions, EvidenceForCommit,
        EventAssurance) ==
    /\ CheckActLicensed(S, PredicateStates, GovernedCommitSteps)
    /\ \A claim \in Claims :
          AtomicCommitEvidenceCoupled(
              EvidenceRequiredActions[claim],
              EvidenceForCommit, EventAssurance)

ProviderBackedRelyPremises(
        S, Components, RelyEdges, RelyRank, RelyPropertyClassOf,
        DirectMutualClosureEdges,
        ComponentObligationStates,
        ComponentRelySteps, ComponentGuaranteeSteps,
        SharedStepsForRelyEdge, RegisteredSharedSteps) ==
    /\ RelyDischargeBoundaryTyped(
           S, Components, RelyEdges, RelyRank, RelyPropertyClassOf,
           DirectMutualClosureEdges,
           ComponentObligationStates,
           ComponentRelySteps, ComponentGuaranteeSteps,
           SharedStepsForRelyEdge)
    /\ RelationTyped(S, RegisteredSharedSteps)
    /\ \A edge \in DirectMutualClosureEdges :
          SharedStepsForRelyEdge[edge] = RegisteredSharedSteps

ProviderBackedRelyConclusion(
        Components, RelyEdges, RelyRank, RelyPropertyClassOf,
        DirectMutualClosureEdges,
        ComponentRelySteps, ComponentGuaranteeSteps) ==
    /\ \A edge \in RelyEdges :
          /\ ComponentGuaranteeSteps[edge[2]] # {}
          /\ ComponentGuaranteeSteps[edge[2]]
               \subseteq ComponentRelySteps[edge[1]]
          /\ RelyRank[edge[2]] < RelyRank[edge[1]]
               \/ /\ edge \in DirectMutualClosureEdges
                  /\ RelyPropertyClassOf[edge] = "safety"
    /\ \A edge \in DirectMutualClosureEdges :
          <<edge[2], edge[1]>> \in DirectMutualClosureEdges

ExactSharedTransitionBoundary(
        S, Components, RepresentedSharedSteps,
        RegisteredSharedSteps, AffectedComponents,
        ComponentObligationStates) ==
    /\ RelationTyped(S, RepresentedSharedSteps)
    /\ RelationTyped(S, RegisteredSharedSteps)
    /\ RegisteredSharedSteps = RepresentedSharedSteps
    /\ AffectedComponents = Components
    /\ Components # {}
    /\ ComponentObligationStates \in [Components -> SUBSET S]

SharedTransitionPreservation(
        S, RegisteredSharedSteps, AffectedComponents,
        ComponentObligationStates) ==
    \A component \in AffectedComponents :
        Stable(
            S, ComponentObligationStates[component],
            RegisteredSharedSteps)

SharedTransitionPremises(
        S, Components, RepresentedSharedSteps,
        RegisteredSharedSteps, AffectedComponents,
        ComponentObligationStates) ==
    /\ ExactSharedTransitionBoundary(
           S, Components, RepresentedSharedSteps,
           RegisteredSharedSteps, AffectedComponents,
           ComponentObligationStates)
    /\ SharedTransitionPreservation(
           S, RegisteredSharedSteps, AffectedComponents,
           ComponentObligationStates)

FailureInputsTyped(
        BypassAbsent, PartitionTolerated, EpochCurrent,
        AssuranceHealthyNow, AuditPersistent,
        ExternalOwnerHealthy, RetryAvailable, RecoveryAvailableNow) ==
    /\ BypassAbsent \in BOOLEAN
    /\ PartitionTolerated \in BOOLEAN
    /\ EpochCurrent \in BOOLEAN
    /\ AssuranceHealthyNow \in BOOLEAN
    /\ AuditPersistent \in BOOLEAN
    /\ ExternalOwnerHealthy \in BOOLEAN
    /\ RetryAvailable \in BOOLEAN
    /\ RecoveryAvailableNow \in BOOLEAN

ExactBypassFailureInputBinding(
        Claims, ActionLabels, Actions,
        ClaimActions, PathClassOf, BypassAbsent) ==
    /\ ClaimActions \in [Claims -> SUBSET ActionLabels]
    /\ PathClassOf \in [Claims -> [ActionLabels -> MediationPathClasses]]
    /\ BypassAbsent \in BOOLEAN
    /\ BypassAbsent =
         (\A claim \in Claims :
              \A action \in BypassActionsFor(
                                  claim, ClaimActions, PathClassOf) :
                  Actions[action] = {})

DerivedFailureCeiling(
        FailureClass, NormalBundle,
        BypassAbsent, PartitionTolerated, EpochCurrent,
        AssuranceHealthyNow, AuditPersistent,
        ExternalOwnerHealthy, RetryAvailable, RecoveryAvailableNow) ==
    CASE FailureClass = "bypass" ->
           IF BypassAbsent THEN NormalBundle ELSE {"lost"}
      [] FailureClass = "partition" ->
           IF PartitionTolerated
             THEN NormalBundle
             ELSE NormalBundle \cap {"conditional", "lost"}
      [] FailureClass = "stale-epoch" ->
           IF EpochCurrent THEN NormalBundle ELSE {"lost"}
      [] FailureClass = "assurance-loss" ->
           IF AssuranceHealthyNow
             THEN NormalBundle
             ELSE NormalBundle \cap {"conditional", "lost"}
      [] FailureClass = "audit-loss" ->
           IF AuditPersistent
             THEN NormalBundle
             ELSE NormalBundle \ {"detection", "recovery"}
      [] FailureClass = "external-owner" ->
           IF ExternalOwnerHealthy
             THEN NormalBundle
             ELSE NormalBundle \ {"prevention"}
      [] FailureClass = "retry-exhaustion" ->
           IF RetryAvailable
             THEN NormalBundle
             ELSE NormalBundle \cap {"conditional", "lost"}
      [] OTHER ->
           IF RecoveryAvailableNow
             THEN NormalBundle
             ELSE NormalBundle \ {"recovery"}

DerivedFailureGuaranteeBundle(
        NormalBundle,
        BypassAbsent, PartitionTolerated, EpochCurrent,
        AssuranceHealthyNow, AuditPersistent,
        ExternalOwnerHealthy, RetryAvailable, RecoveryAvailableNow) ==
    [failureClass \in ALKFailureClasses |->
        DerivedFailureCeiling(
            failureClass, NormalBundle,
            BypassAbsent, PartitionTolerated, EpochCurrent,
            AssuranceHealthyNow, AuditPersistent,
            ExternalOwnerHealthy, RetryAvailable, RecoveryAvailableNow)]

NamedFailureNarrowingConclusion(
        NormalBundle,
        BypassAbsent, PartitionTolerated, EpochCurrent,
        AssuranceHealthyNow, AuditPersistent,
        ExternalOwnerHealthy, RetryAvailable, RecoveryAvailableNow) ==
    LET Result ==
          DerivedFailureGuaranteeBundle(
              NormalBundle,
              BypassAbsent, PartitionTolerated, EpochCurrent,
              AssuranceHealthyNow, AuditPersistent,
              ExternalOwnerHealthy, RetryAvailable,
              RecoveryAvailableNow)
    IN
    /\ NormalBundle \subseteq GuaranteeKinds
    /\ \A failureClass \in ALKFailureClasses :
          Result[failureClass] \subseteq NormalBundle \cup {"lost"}
    /\ ~BypassAbsent => Result["bypass"] = {"lost"}
    /\ ~PartitionTolerated
         => Result["partition"] \subseteq {"conditional", "lost"}
    /\ ~EpochCurrent => Result["stale-epoch"] = {"lost"}
    /\ ~AssuranceHealthyNow
         => Result["assurance-loss"]
              \subseteq {"conditional", "lost"}
    /\ ~AuditPersistent
         => /\ "detection" \notin Result["audit-loss"]
            /\ "recovery" \notin Result["audit-loss"]
    /\ ~ExternalOwnerHealthy
         => "prevention" \notin Result["external-owner"]
    /\ ~RetryAvailable
         => Result["retry-exhaustion"]
              \subseteq {"conditional", "lost"}
    /\ ~RecoveryAvailableNow
         => "recovery" \notin Result["recovery-failure"]

FailureGuaranteeBundleMatchesDerived(
        AdvertisedUnderFailure, NormalBundle,
        BypassAbsent, PartitionTolerated, EpochCurrent,
        AssuranceHealthyNow, AuditPersistent,
        ExternalOwnerHealthy, RetryAvailable, RecoveryAvailableNow) ==
    /\ AdvertisedUnderFailure
         \in [ALKFailureClasses -> SUBSET GuaranteeKinds]
    /\ AdvertisedUnderFailure =
         DerivedFailureGuaranteeBundle(
             NormalBundle,
             BypassAbsent, PartitionTolerated, EpochCurrent,
             AssuranceHealthyNow, AuditPersistent,
             ExternalOwnerHealthy, RetryAvailable,
             RecoveryAvailableNow)

RequiredClaimDependenciesFor(
        claim, ClaimObligations, ObligationPropertyClass,
        LivenessFairnessOwner,
        GuaranteeClaimant, ALKAuthority,
        AdmittedActions, ClaimCommitActions,
        OwnerOf, DelegateOf, AssuranceProviderOf,
        ActorDependency, EvidenceForCommit,
        EvidenceProducer, CustodianOf, RetentionProviderOf,
        ProviderDependency) ==
    LET ClaimEvidenceEvents ==
          UNION {EvidenceForCommit[action] :
                    action \in ClaimCommitActions[claim]}
        SelectedLivenessObligations ==
          SelectedLivenessObligationsFor(
              claim, ClaimObligations, ObligationPropertyClass)
    IN
    {ActorDependency[GuaranteeClaimant[claim]]}
      \cup {ActorDependency[actor] : actor \in ALKAuthority[claim]}
      \cup {ActorDependency[OwnerOf[action]] :
               action \in AdmittedActions[claim]}
      \cup UNION {
             {ActorDependency[actor] : actor \in DelegateOf[action]} :
             action \in AdmittedActions[claim]}
      \cup {ProviderDependency[AssuranceProviderOf[action]] :
               action \in ClaimCommitActions[claim]}
      \cup {ActorDependency[EvidenceProducer[event]] :
               event \in ClaimEvidenceEvents}
      \cup {ActorDependency[CustodianOf[event]] :
               event \in ClaimEvidenceEvents}
      \cup {ProviderDependency[RetentionProviderOf[event]] :
               event \in ClaimEvidenceEvents}
      \cup {ActorDependency[LivenessFairnessOwner[obligation]] :
               obligation \in SelectedLivenessObligations}

ExactClaimTCBClosure(
        Claims, Obligations, ActionLabels, Actors, Providers,
        EvidenceEvents, Dependencies, ClaimTCB,
        ClaimObligations, ObligationPropertyClass,
        LivenessFairnessOwner,
        GuaranteeClaimant, ALKAuthority,
        AdmittedActions, ClaimCommitActions,
        OwnerOf, DelegateOf, AssuranceProviderOf,
        ActorDependency, EvidenceForCommit,
        EvidenceProducer, CustodianOf, RetentionProviderOf,
        ProviderDependency) ==
    LET AllCommitActions ==
          UNION {ClaimCommitActions[claim] : claim \in Claims}
    IN
    /\ Actors \cap Dependencies = {}
    /\ ClaimTCB \in [Claims -> SUBSET Dependencies]
    /\ ClaimObligations \in [Claims -> SUBSET Obligations]
    /\ ObligationPropertyClass \in [Obligations -> PropertyClasses]
    /\ LivenessFairnessOwner \in [Obligations -> Actors]
    /\ GuaranteeClaimant \in [Claims -> Actors]
    /\ ALKAuthority \in [Claims -> SUBSET Actors]
    /\ AdmittedActions \in [Claims -> SUBSET ActionLabels]
    /\ ClaimCommitActions \in [Claims -> SUBSET ActionLabels]
    /\ OwnerOf \in [ActionLabels -> Actors]
    /\ DelegateOf \in [ActionLabels -> SUBSET Actors]
    /\ AssuranceProviderOf \in [ActionLabels -> Providers]
    /\ ActorDependency \in [Actors -> Dependencies]
    /\ EvidenceForCommit \in [AllCommitActions -> SUBSET EvidenceEvents]
    /\ EvidenceProducer \in [EvidenceEvents -> Actors]
    /\ CustodianOf \in [EvidenceEvents -> Actors]
    /\ RetentionProviderOf \in [EvidenceEvents -> Providers]
    /\ ProviderDependency \in [Providers -> Dependencies]
    /\ \A claim \in Claims :
          RequiredClaimDependenciesFor(
              claim, ClaimObligations, ObligationPropertyClass,
              LivenessFairnessOwner,
              GuaranteeClaimant, ALKAuthority,
              AdmittedActions, ClaimCommitActions,
              OwnerOf, DelegateOf, AssuranceProviderOf,
              ActorDependency, EvidenceForCommit,
              EvidenceProducer, CustodianOf, RetentionProviderOf,
              ProviderDependency)
            \subseteq ClaimTCB[claim]

MechanicallyRequiredClaimDependencies(
        Claims, ClaimObligations, ObligationPropertyClass,
        LivenessFairnessOwner,
        GuaranteeClaimant, ALKAuthority,
        AdmittedActions, ClaimCommitActions,
        OwnerOf, DelegateOf, AssuranceProviderOf,
        ActorDependency, EvidenceForCommit,
        EvidenceProducer, CustodianOf, RetentionProviderOf,
        ProviderDependency) ==
    UNION {
        RequiredClaimDependenciesFor(
            claim, ClaimObligations, ObligationPropertyClass,
            LivenessFairnessOwner,
            GuaranteeClaimant, ALKAuthority,
            AdmittedActions, ClaimCommitActions,
            OwnerOf, DelegateOf, AssuranceProviderOf,
            ActorDependency, EvidenceForCommit,
            EvidenceProducer, CustodianOf, RetentionProviderOf,
            ProviderDependency) :
        claim \in Claims}

ExactTCBRequirementGrowthBinding(
        Claims, Dependencies,
        ClaimObligations, ObligationPropertyClass,
        LivenessFairnessOwner,
        GuaranteeClaimant, ALKAuthority,
        AdmittedActions, ClaimCommitActions,
        OwnerOf, DelegateOf, AssuranceProviderOf,
        ActorDependency, EvidenceForCommit,
        EvidenceProducer, CustodianOf, RetentionProviderOf,
        ProviderDependency,
        RequiredBefore, AddedRequired) ==
    LET CurrentRequired ==
          MechanicallyRequiredClaimDependencies(
              Claims, ClaimObligations, ObligationPropertyClass,
              LivenessFairnessOwner,
              GuaranteeClaimant, ALKAuthority,
              AdmittedActions, ClaimCommitActions,
              OwnerOf, DelegateOf, AssuranceProviderOf,
              ActorDependency, EvidenceForCommit,
              EvidenceProducer, CustodianOf, RetentionProviderOf,
              ProviderDependency)
    IN
    /\ Cardinality(Claims) = 1
    /\ RequiredBefore = CurrentRequired
    /\ RequiredBefore \subseteq Dependencies
    /\ AddedRequired \subseteq Dependencies
    /\ AddedRequired \cap RequiredBefore = {}

SufficientTCBs(Dependencies, RequiredDependencies) ==
    {candidate \in SUBSET Dependencies :
        RequiredDependencies \subseteq candidate}

FixedClaimTCBMonotonicity(
        Dependencies, RequiredBefore, AddedRequired) ==
    /\ RequiredBefore \subseteq Dependencies
    /\ AddedRequired \subseteq Dependencies
    /\ SufficientTCBs(
           Dependencies, RequiredBefore \cup AddedRequired)
         \subseteq SufficientTCBs(Dependencies, RequiredBefore)
    /\ \A candidate \in SufficientTCBs(
                           Dependencies,
                           RequiredBefore \cup AddedRequired) :
          /\ RequiredBefore \subseteq candidate
          /\ AddedRequired \subseteq candidate

ClaimBearingKernelGuarantees(RegisteredGuarantees, GuaranteeFamily) ==
    {guarantee \in RegisteredGuarantees :
        GuaranteeFamily[guarantee]
          \in {"obligation", "progress", "refinement"}}

KernelGuaranteeObligationClassCompatible(
        GuaranteeClass, ObligationClass) ==
    \/ GuaranteeClass = ObligationClass
    \/ /\ GuaranteeClass = "evidence"
       /\ ObligationClass \in {"safety", "evidence"}

SelectedObligationStates(
        StateDomain, SelectedObligations, ObligationStates) ==
    {state \in StateDomain :
        \A obligation \in SelectedObligations :
          state \in ObligationStates[obligation]}

KernelSelectionGuaranteeBinding(
        Claims, Structures, ExecutionModalities, Obligations,
        StateDomain,
        SelectedStructures, SelectedExecutionModality,
        ClaimObligations, ObligationPropertyClass, ObligationStates,
        KernelSelectedStructures, KernelSelectedExecutionCarrier,
        RegisteredGuarantees, GuaranteeFamily,
        GuaranteePropertyClass, GuaranteeObligations,
        RegisteredObligationStates) ==
    LET ClaimBearingGuarantees ==
          ClaimBearingKernelGuarantees(
              RegisteredGuarantees, GuaranteeFamily)
    IN
    /\ Cardinality(Claims) = 1
    /\ SelectedStructures \in [Claims -> SUBSET Structures]
    /\ SelectedExecutionModality \in [Claims -> ExecutionModalities]
    /\ ClaimObligations \in [Claims -> SUBSET Obligations]
    /\ ObligationPropertyClass \in [Obligations -> PropertyClasses]
    /\ ObligationStates \in [Obligations -> SUBSET StateDomain]
    /\ GuaranteeObligations
         \in [RegisteredGuarantees -> SUBSET Obligations]
    /\ \A claim \in Claims :
          /\ KernelSelectedStructures =
               SelectedStructures[claim]
                 \cup {SelectedExecutionModality[claim]}
          /\ KernelSelectedExecutionCarrier =
               SelectedExecutionModality[claim]
          /\ ClaimObligations[claim] # {}
          /\ ClaimBearingGuarantees # {}
          /\ \A guarantee \in ClaimBearingGuarantees :
                /\ GuaranteeObligations[guarantee] # {}
                /\ GuaranteeObligations[guarantee]
                     \subseteq ClaimObligations[claim]
                /\ \A obligation \in
                          GuaranteeObligations[guarantee] :
                      KernelGuaranteeObligationClassCompatible(
                          GuaranteePropertyClass[guarantee],
                          ObligationPropertyClass[obligation])
          /\ UNION {GuaranteeObligations[guarantee] :
                       guarantee \in ClaimBearingGuarantees}
               = ClaimObligations[claim]
          /\ RegisteredObligationStates =
               SelectedObligationStates(
                   StateDomain, ClaimObligations[claim],
                   ObligationStates)

DirectOrDelegatedCommitSet(CommitOwner, CommitDelegate) ==
    IF CommitDelegate = CommitOwner THEN {} ELSE {CommitDelegate}

KernelCommitAssuranceBinding(
        Claims, ActionLabels, PotentialActions, PostMediationSteps,
        ClaimCommitActions, GuaranteeClaimant, OwnerOf, DelegateOf,
        AssuranceProviderOf, AssurancePositionOf,
        PreventionControllers, UnavailableProviders,
        PersistentEvidenceFor, RecoveryAvailableFor,
        FormalCommitSteps, FormalCommitOwner, FormalCommitDelegate,
        FormalCommitAssurance,
        KernelClaimant, KernelAssuranceProvider,
        KernelPreventionControllers, KernelUnavailableProviders,
        KernelPersistentEvidence, KernelRecoveryAvailable) ==
    /\ \A claim \in Claims :
          /\ GuaranteeClaimant[claim] = KernelClaimant
          /\ PreventionControllers = KernelPreventionControllers
          /\ UnavailableProviders = KernelUnavailableProviders
           /\ FormalCommitSteps =
                UNION {
                    PostMediationSteps[action] \cap FormalCommitSteps :
                    action \in ClaimCommitActions[claim]}
           /\ \A action \in ClaimCommitActions[claim] :
                /\ PotentialActions[action] \cap FormalCommitSteps =
                     PostMediationSteps[action] \cap FormalCommitSteps
                /\ AssuranceProviderOf[action] =
                     KernelAssuranceProvider
                /\ PersistentEvidenceFor[action] =
                     KernelPersistentEvidence
                /\ RecoveryAvailableFor[action] =
                     KernelRecoveryAvailable
                /\ \A step \in
                          PostMediationSteps[action] \cap FormalCommitSteps :
                      /\ FormalCommitOwner[step] = OwnerOf[action]
                      /\ DelegateOf[action] =
                           DirectOrDelegatedCommitSet(
                               OwnerOf[action],
                               FormalCommitDelegate[step])
                      /\ FormalCommitAssurance[step] =
                           AssurancePositionOf[action]

KernelCompositionBinding(
        Components, RelyEdges,
        ComponentObligationStates,
        ComponentRelySteps, ComponentGuaranteeSteps,
        RegisteredSharedSteps,
        KernelRelyEdges, KernelInvA, KernelInvB,
        KernelRelyA, KernelRelyB,
        KernelStepA, KernelStepB, KernelSharedSteps) ==
    /\ Components = CompositionComponents
    /\ RelyEdges = KernelRelyEdges
    /\ ComponentObligationStates =
         [component \in CompositionComponents |->
             IF component = "component-a"
               THEN KernelInvA
               ELSE KernelInvB]
    /\ ComponentRelySteps =
         [component \in CompositionComponents |->
             IF component = "component-a"
               THEN KernelRelyA
               ELSE KernelRelyB]
    /\ ComponentGuaranteeSteps =
         [component \in CompositionComponents |->
             IF component = "component-a"
               THEN KernelStepA
               ELSE KernelStepB]
    /\ RegisteredSharedSteps = KernelSharedSteps

KernelEvidenceBinding(
        Claims, ALKEvidenceEvents, KernelEvidenceEvents,
        EvidenceRequiredActions, EvidenceForCommit,
        FormalCommitSteps,
        ALKEvidenceKernelEvent,
        ALKEventObservation,
        ALKEventSubject, ALKEventAction,
        ALKEventClaimant, ALKEventOwner,
        ALKEventCommit, ALKEventAssurance, ALKEventEvidenceClass,
        PostMediationSteps,
        KernelEventObservation,
        KernelEventSubject, KernelEventAction,
        KernelEventClaimant, KernelEventOwner,
        KernelEventCommit, KernelEventAssurance,
        KernelEventEvidenceClass) ==
    /\ ALKEvidenceKernelEvent
         \in [ALKEvidenceEvents -> KernelEvidenceEvents]
    /\ ALKEventObservation
         \in [ALKEvidenceEvents ->
                {KernelEventObservation[event] :
                    event \in KernelEvidenceEvents}]
    /\ ALKEventEvidenceClass
         \in [ALKEvidenceEvents -> KernelTracePropertyClasses]
    /\ EvidenceRequiredActions
         \in [Claims -> SUBSET DOMAIN EvidenceForCommit]
    /\ KernelEvidenceEvents =
         {ALKEvidenceKernelEvent[event] : event \in ALKEvidenceEvents}
    /\ \A left \in ALKEvidenceEvents,
          right \in ALKEvidenceEvents :
          ALKEvidenceKernelEvent[left] = ALKEvidenceKernelEvent[right]
            => left = right
    /\ \A event \in ALKEvidenceEvents :
          LET kernelEvent == ALKEvidenceKernelEvent[event]
          IN  /\ KernelEventObservation[kernelEvent] =
                   ALKEventObservation[event]
              /\ KernelEventSubject[kernelEvent] = ALKEventSubject[event]
              /\ KernelEventClaimant[kernelEvent] =
                   ALKEventClaimant[event]
              /\ KernelEventOwner[kernelEvent] = ALKEventOwner[event]
              /\ KernelEventAssurance[kernelEvent] =
                   ALKEventAssurance[event]
              /\ KernelEventCommit[kernelEvent]
                   \in PostMediationSteps[ALKEventCommit[event]]
              /\ KernelEventAction[kernelEvent]
                   \in PostMediationSteps[ALKEventAction[event]]
              /\ KernelEventCommit[kernelEvent] =
                   KernelEventAction[kernelEvent]
              /\ KernelEventEvidenceClass[kernelEvent] =
                   ALKEventEvidenceClass[event]
    /\ \A claim \in Claims :
          \A action \in EvidenceRequiredActions[claim] :
              PostMediationSteps[action] \cap FormalCommitSteps =
                {KernelEventCommit[ALKEvidenceKernelEvent[event]] :
                    event \in EvidenceForCommit[action]}

====
