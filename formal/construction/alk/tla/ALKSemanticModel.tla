---- MODULE ALKSemanticModel ----
EXTENDS CommonSemanticSchema

MediationPathClasses == {"mediated", "external", "bypass", "excluded"}

ALKFailureClasses ==
    {"bypass", "partition", "stale-epoch", "assurance-loss",
     "audit-loss", "external-owner", "retry-exhaustion",
     "recovery-failure"}

ResidualClasses ==
    {"external-service", "host-mechanism", "domain-policy",
     "unobserved-detail", "outside-claim"}

ObservationDimensions ==
    {"state", "ordering", "multiplicity", "timing", "failure", "identity"}

RetainedPrimitiveNames ==
    {"Budget", "QualityHierarchy", "ResourceRegistry",
     "CompetitiveSelection", "ActuationPass", "PropagationPass",
     "ConvergenceGovernor", "AuditSink", "BacktrackingTraversal"}

RetainedCompositionNames ==
    {"AllocationSnapshot", "FederatedBudget", "Bisection",
     "EquivalenceClass", "RateLimit", "Reduction",
     "RelationshipGraph", "Sampler", "Signal", "TraversalEngine"}

RetainedStructureNames ==
    RetainedPrimitiveNames \cup RetainedCompositionNames

RetainedConnectiveNames ==
    {"Projection", "Cursor", "Accumulator", "Marker",
     "Counter", "Buffer", "OrderingPass"}

RetainedExecutionModalityNames ==
    {"Sequential", "ForkJoin", "StepGraph", "StreamGraph"}

RetainedRegistryBindingTyped(
        RegistryPrimitives, RegistryCompositions,
        RegistryConnectives, RegistryModalities,
        RegistryOccurrences, RegistryEquivalentOccurrences,
        RegistryLocalNames,
        RegistryCanonicalNames, RegistryNormalizedObligations,
        RegistryPropertyClasses,
        RegistryKindOf, RegistryOccurrenceStructure,
        RegistryOccurrenceLocalNameOf,
        RegistryCanonicalNameOf, RegistryNormalizedKeyOf,
        RegistryPropertyClassOf,
        RegistryCarrierObligationOccurrences) ==
    LET RegistryCarriers ==
            RegistryPrimitives \cup RegistryCompositions \cup RegistryModalities
    IN  /\ RegistryPrimitives = RetainedPrimitiveNames
        /\ RegistryCompositions = RetainedCompositionNames
        /\ RegistryConnectives = RetainedConnectiveNames
        /\ RegistryModalities = RetainedExecutionModalityNames
        /\ RegistryOccurrences # {}
        /\ RegistryEquivalentOccurrences
             \subseteq RegistryOccurrences \X RegistryOccurrences
        /\ RegistryLocalNames # {}
        /\ RegistryCanonicalNames # {}
        /\ RegistryNormalizedObligations # {}
        /\ RegistryPropertyClasses # {}
        /\ RegistryPropertyClasses \subseteq PropertyClasses
        /\ RegistryKindOf
             \in [RegistryCarriers ->
                    {"abstraction-primitive", "named-composition",
                     "execution-modality"}]
        /\ RegistryOccurrenceStructure
             \in [RegistryOccurrences -> RegistryCarriers]
        /\ RegistryOccurrenceLocalNameOf
             \in [RegistryOccurrences -> RegistryLocalNames]
        /\ RegistryCanonicalNameOf
             \in [RegistryOccurrences -> RegistryCanonicalNames]
        /\ RegistryNormalizedKeyOf
             \in [RegistryOccurrences -> RegistryNormalizedObligations]
        /\ RegistryPropertyClassOf
             \in [RegistryOccurrences -> RegistryPropertyClasses]
        /\ RegistryCarrierObligationOccurrences
             \in [RegistryCarriers -> SUBSET RegistryOccurrences]
        /\ RegistryLocalNames =
             {RegistryOccurrenceLocalNameOf[occurrence] :
                occurrence \in RegistryOccurrences}
        /\ RegistryCanonicalNames =
             {RegistryCanonicalNameOf[occurrence] :
                occurrence \in RegistryOccurrences}
        /\ RegistryNormalizedObligations =
             {RegistryNormalizedKeyOf[occurrence] :
                occurrence \in RegistryOccurrences}
        /\ RegistryPropertyClasses =
             {RegistryPropertyClassOf[occurrence] :
                occurrence \in RegistryOccurrences}
        /\ \A left \in RegistryOccurrences,
              right \in RegistryOccurrences :
              (RegistryNormalizedKeyOf[left]
                 = RegistryNormalizedKeyOf[right])
                <=> (left = right
                       \/ <<left, right>>
                            \in RegistryEquivalentOccurrences)
        /\ \A primitive \in RegistryPrimitives :
             RegistryKindOf[primitive] = "abstraction-primitive"
        /\ \A composition \in RegistryCompositions :
             RegistryKindOf[composition] = "named-composition"
        /\ \A modality \in RegistryModalities :
             RegistryKindOf[modality] = "execution-modality"
        /\ \A carrier \in RegistryCarriers :
             /\ RegistryCarrierObligationOccurrences[carrier] # {}
             /\ RegistryCarrierObligationOccurrences[carrier] =
                  {occurrence \in RegistryOccurrences :
                      RegistryOccurrenceStructure[occurrence] = carrier}
        /\ UNION {RegistryCarrierObligationOccurrences[carrier] :
                    carrier \in RegistryCarriers} = RegistryOccurrences

RetainedConstructionBindingTyped(
        ObligationOccurrences, Structures, ExecutionModalities,
        StructureObligationOccurrences,
        ExecutionModalityObligationOccurrences,
        NormalizedKeyOf, ObligationPropertyClassOf,
        ProvedEquivalentOccurrences,
        RegistryOccurrences, RegistryEquivalentOccurrences,
        RegistryCarrierObligationOccurrences,
        RegistryNormalizedKeyOf, RegistryPropertyClassOf) ==
    /\ RegistryOccurrences \subseteq ObligationOccurrences
    /\ ProvedEquivalentOccurrences = RegistryEquivalentOccurrences
    /\ Structures = RetainedStructureNames
    /\ ExecutionModalities = RetainedExecutionModalityNames
    /\ StructureObligationOccurrences
         \in [Structures -> SUBSET ObligationOccurrences]
    /\ ExecutionModalityObligationOccurrences
         \in [ExecutionModalities -> SUBSET ObligationOccurrences]
    /\ NormalizedKeyOf \in [ObligationOccurrences -> STRING]
    /\ ObligationPropertyClassOf
         \in [ObligationOccurrences -> PropertyClasses]
    /\ RegistryCarrierObligationOccurrences
         \in [Structures \cup ExecutionModalities -> SUBSET RegistryOccurrences]
    /\ RegistryNormalizedKeyOf \in [RegistryOccurrences -> STRING]
    /\ RegistryPropertyClassOf
         \in [RegistryOccurrences -> PropertyClasses]
    /\ \A structure \in Structures :
          StructureObligationOccurrences[structure] =
              RegistryCarrierObligationOccurrences[structure]
    /\ \A modality \in ExecutionModalities :
          ExecutionModalityObligationOccurrences[modality] =
              RegistryCarrierObligationOccurrences[modality]
    /\ \A occurrence \in RegistryOccurrences :
          /\ NormalizedKeyOf[occurrence] = RegistryNormalizedKeyOf[occurrence]
          /\ ObligationPropertyClassOf[occurrence] =
               RegistryPropertyClassOf[occurrence]

NormalizedObligations(Occurrences, NormalizedKeyOf) ==
    {NormalizedKeyOf[occurrence] : occurrence \in Occurrences}

ObligationNormalizationTyped(
        ObligationOccurrences, Obligations,
        PredicateIds, ScopeIds, ObservationBoundaryIds,
        FailureCeilingIds, PropertyClassesUsed,
        Actors, CommitBoundaryIds,
        NormalizedKeyOf, PredicateOf, ScopeOf,
        ObligationObservationBoundaryOf, ObligationFailureCeilingOf,
        ObligationPropertyClassOf, ObligationPropertyClass,
        OccurrenceOwner,
        OccurrenceCommitBoundary,
        ProvedEquivalentOccurrences) ==
    /\ ObligationOccurrences # {}
    /\ Obligations # {}
    /\ PropertyClassesUsed # {}
    /\ PropertyClassesUsed \subseteq PropertyClasses
    /\ NormalizedKeyOf \in [ObligationOccurrences -> Obligations]
    /\ PredicateOf \in [ObligationOccurrences -> PredicateIds]
    /\ ScopeOf \in [ObligationOccurrences -> ScopeIds]
    /\ ObligationObservationBoundaryOf
         \in [ObligationOccurrences -> ObservationBoundaryIds]
    /\ ObligationFailureCeilingOf
         \in [ObligationOccurrences -> FailureCeilingIds]
    /\ ObligationPropertyClassOf
         \in [ObligationOccurrences -> PropertyClassesUsed]
    /\ ObligationPropertyClass
         \in [Obligations -> PropertyClassesUsed]
    /\ OccurrenceOwner \in [ObligationOccurrences -> Actors]
    /\ OccurrenceCommitBoundary
         \in [ObligationOccurrences -> CommitBoundaryIds]
    /\ ProvedEquivalentOccurrences
         \subseteq ObligationOccurrences \X ObligationOccurrences
    /\ Obligations =
         NormalizedObligations(ObligationOccurrences, NormalizedKeyOf)
    /\ \A occurrence \in ObligationOccurrences :
          ObligationPropertyClass[NormalizedKeyOf[occurrence]] =
              ObligationPropertyClassOf[occurrence]
    /\ \A left \in ObligationOccurrences,
          right \in ObligationOccurrences :
          /\ (NormalizedKeyOf[left] = NormalizedKeyOf[right])
               <=> (left = right
                      \/ <<left, right>> \in ProvedEquivalentOccurrences)
          /\ (NormalizedKeyOf[left] = NormalizedKeyOf[right]
            => /\ PredicateOf[left] = PredicateOf[right]
               /\ ScopeOf[left] = ScopeOf[right]
               /\ ObligationObservationBoundaryOf[left]
                    = ObligationObservationBoundaryOf[right]
               /\ ObligationFailureCeilingOf[left]
                    = ObligationFailureCeilingOf[right]
               /\ ObligationPropertyClassOf[left]
                    = ObligationPropertyClassOf[right]
               /\ OccurrenceOwner[left] = OccurrenceOwner[right]
               /\ OccurrenceCommitBoundary[left]
                    = OccurrenceCommitBoundary[right])

RequiredALKObligationOccurrences(
        SelectedStructures, SelectedExecutionModality,
        StructureObligationOccurrences,
        ExecutionModalityObligationOccurrences,
        CompositionSeamObligationOccurrences) ==
    UNION {StructureObligationOccurrences[structure] :
              structure \in SelectedStructures}
      \cup ExecutionModalityObligationOccurrences[SelectedExecutionModality]
      \cup CompositionSeamObligationOccurrences

RequiredALKObligations(
        SelectedStructures, SelectedExecutionModality,
        StructureObligationOccurrences,
        ExecutionModalityObligationOccurrences,
        CompositionSeamObligationOccurrences,
        NormalizedKeyOf) ==
    NormalizedObligations(
        RequiredALKObligationOccurrences(
            SelectedStructures, SelectedExecutionModality,
            StructureObligationOccurrences,
            ExecutionModalityObligationOccurrences,
            CompositionSeamObligationOccurrences),
        NormalizedKeyOf)

ALKKernelVocabularyTyped(
        Structures, Connectives, ExecutionModalities,
        ObligationOccurrences, Obligations,
        StructureObligationOccurrences,
        ExecutionModalityObligationOccurrences,
        NormalizedKeyOf,
        StructureObligations, ExecutionModalityObligations) ==
    /\ Structures = RetainedStructureNames
    /\ Connectives = RetainedConnectiveNames
    /\ ExecutionModalities = RetainedExecutionModalityNames
    /\ StructureObligationOccurrences
         \in [Structures -> SUBSET ObligationOccurrences]
    /\ ExecutionModalityObligationOccurrences
         \in [ExecutionModalities -> SUBSET ObligationOccurrences]
    /\ StructureObligations \in [Structures -> SUBSET Obligations]
    /\ ExecutionModalityObligations
         \in [ExecutionModalities -> SUBSET Obligations]
    /\ \A structure \in Structures :
          /\ StructureObligationOccurrences[structure] # {}
          /\ StructureObligations[structure] =
               NormalizedObligations(
                   StructureObligationOccurrences[structure],
                   NormalizedKeyOf)
    /\ \A modality \in ExecutionModalities :
          /\ ExecutionModalityObligationOccurrences[modality] # {}
          /\ ExecutionModalityObligations[modality] =
               NormalizedObligations(
                   ExecutionModalityObligationOccurrences[modality],
                   NormalizedKeyOf)
    /\ \A left \in Structures, right \in Structures :
          left # right
            => StructureObligationOccurrences[left]
                 \cap StructureObligationOccurrences[right] = {}
    /\ \A left \in ExecutionModalities,
          right \in ExecutionModalities :
          left # right
            => ExecutionModalityObligationOccurrences[left]
                 \cap ExecutionModalityObligationOccurrences[right] = {}
    /\ \A structure \in Structures, modality \in ExecutionModalities :
          StructureObligationOccurrences[structure]
            \cap ExecutionModalityObligationOccurrences[modality] = {}

ALKConstructionSelectionTyped(
        Claims, Structures, ExecutionModalities,
        ObligationOccurrences, Obligations,
        StructureObligationOccurrences,
        ExecutionModalityObligationOccurrences,
        NormalizedKeyOf,
        SelectedStructures, SelectedExecutionModality,
        CompositionSeamObligationOccurrences,
        ClaimObligationOccurrences, ClaimObligations) ==
    /\ SelectedStructures \in [Claims -> SUBSET Structures]
    /\ SelectedExecutionModality \in [Claims -> ExecutionModalities]
    /\ CompositionSeamObligationOccurrences
         \in [Claims -> SUBSET ObligationOccurrences]
    /\ ClaimObligationOccurrences
         \in [Claims -> SUBSET ObligationOccurrences]
    /\ ClaimObligations \in [Claims -> SUBSET Obligations]
    /\ \A claim \in Claims :
          /\ SelectedStructures[claim] # {}
          /\ ClaimObligationOccurrences[claim] =
               RequiredALKObligationOccurrences(
                   SelectedStructures[claim],
                   SelectedExecutionModality[claim],
                   StructureObligationOccurrences,
                   ExecutionModalityObligationOccurrences,
                   CompositionSeamObligationOccurrences[claim])
          /\ ClaimObligations[claim] =
               RequiredALKObligations(
                   SelectedStructures[claim],
                   SelectedExecutionModality[claim],
                   StructureObligationOccurrences,
                   ExecutionModalityObligationOccurrences,
                   CompositionSeamObligationOccurrences[claim],
                   NormalizedKeyOf)

ClaimAnchorTyped(
        Claims, Subjects, Obligations, Scopes, Actors, FailureModels,
        ClaimSubject, ClaimObligations, ClaimScope,
        GuaranteeClaimant, ClaimFailureModel) ==
    /\ Claims # {}
    /\ ClaimSubject \in [Claims -> Subjects]
    /\ ClaimObligations \in [Claims -> SUBSET Obligations]
    /\ ClaimScope \in [Claims -> Scopes]
    /\ GuaranteeClaimant \in [Claims -> Actors]
    /\ ClaimFailureModel \in [Claims -> FailureModels]
    /\ \A claim \in Claims : ClaimObligations[claim] # {}

RepresentedFalsifier(
        S, Actions, ObligationStates, ViolationStates, action) ==
    \E pair \in Actions[action] :
        /\ pair[1] \in ObligationStates
        /\ pair[2] \in ViolationStates

RepresentedViolatingActionsFor(
        S, ActionLabels, Actions, ObligationStates, ViolationStates) ==
    {action \in ActionLabels :
        RepresentedFalsifier(
            S, Actions, ObligationStates, ViolationStates, action)}

RepresentedRelationalViolatingActionsFor(
        ActionLabels, Actions, AllowedRelationSteps) ==
    {action \in ActionLabels :
        \E pair \in Actions[action] : pair \notin AllowedRelationSteps}

ExpectedViolatingActionsFor(
        obligation, S, ActionLabels, Actions,
        ObligationPropertyClass, ObligationStates, ViolationStates,
        AllowedRelationSteps) ==
    CASE ObligationPropertyClass[obligation] = "liveness" -> {}
      [] ObligationPropertyClass[obligation] = "relational" ->
           RepresentedRelationalViolatingActionsFor(
               ActionLabels, Actions, AllowedRelationSteps[obligation])
      [] OTHER ->
           RepresentedViolatingActionsFor(
               S, ActionLabels, Actions,
               ObligationStates[obligation], ViolationStates[obligation])

RankedLivenessObligationTyped(
        S, ActionLabels, Actions,
        ActiveStates, ClosedStates,
        ProgressActions, OtherActions, WeakFairProgressActions,
        RankBound, Rank,
        FairnessActors, FairnessOwner, FairnessOwnerOf) ==
    LET ProgressSteps == ActionUnion(ProgressActions, Actions)
        OtherSteps == ActionUnion(OtherActions, Actions)
    IN  /\ ActiveStates = S \ ClosedStates
        /\ ActiveStates # {}
        /\ ProgressMeasureTyped(S, ClosedStates, RankBound, Rank)
        /\ ProgressActions \subseteq ActionLabels
        /\ ProgressActions # {}
        /\ OtherActions = ActionLabels \ ProgressActions
        /\ WeakFairProgressActions = ProgressActions
        /\ \A action \in ProgressActions : Actions[action] # {}
        /\ FairnessActors # {}
        /\ FairnessOwner \in FairnessActors
        /\ FairnessOwnerOf \in [ActionLabels -> FairnessActors]
        /\ \A action \in ProgressActions :
              FairnessOwnerOf[action] = FairnessOwner
        /\ \A pair \in ProgressSteps :
              /\ pair[1] \in ActiveStates
              /\ Rank[pair[2]] < Rank[pair[1]]
        /\ \A pair \in OtherSteps :
              Rank[pair[2]] <= Rank[pair[1]]
        /\ \A state \in ActiveStates :
              \E pair \in ProgressSteps : pair[1] = state

NoUnprovedObligationDerivation(Obligations, DerivedFrom) ==
    /\ DerivedFrom \in [Obligations -> SUBSET Obligations]
    /\ \A obligation \in Obligations : DerivedFrom[obligation] = {}

SelectedObligationBoundaryTyped(
        S, ActionLabels, Actions, Claims, Obligations, Actors,
        ObligationPropertyClass,
        ClaimObligations, ObligationStates, ViolationStates,
        AllowedRelationSteps, ViolatingActions,
        DerivedFrom,
        LivenessActiveStates, LivenessClosedStates,
        LivenessProgressActions, LivenessOtherActions,
        LivenessWeakFairProgressActions,
        LivenessRankBound, LivenessRank,
        LivenessFairnessOwner, LivenessFairnessOwnerOf) ==
    /\ S # {}
    /\ ActionFamilyTyped(S, ActionLabels, Actions)
    /\ ClaimObligations \in [Claims -> SUBSET Obligations]
    /\ ObligationPropertyClass \in [Obligations -> PropertyClasses]
    /\ ObligationStates \in [Obligations -> SUBSET S]
    /\ ViolationStates \in [Obligations -> SUBSET S]
    /\ AllowedRelationSteps \in [Obligations -> SUBSET Pairs(S)]
    /\ ViolatingActions \in [Obligations -> SUBSET ActionLabels]
    /\ NoUnprovedObligationDerivation(Obligations, DerivedFrom)
    /\ LivenessActiveStates \in [Obligations -> SUBSET S]
    /\ LivenessClosedStates \in [Obligations -> SUBSET S]
    /\ LivenessProgressActions
         \in [Obligations -> SUBSET ActionLabels]
    /\ LivenessOtherActions \in [Obligations -> SUBSET ActionLabels]
    /\ LivenessWeakFairProgressActions
         \in [Obligations -> SUBSET ActionLabels]
    /\ LivenessRankBound \in [Obligations -> Nat]
    /\ LivenessRank \in [Obligations -> [S -> Nat]]
    /\ LivenessFairnessOwner \in [Obligations -> Actors]
    /\ LivenessFairnessOwnerOf
         \in [Obligations -> [ActionLabels -> Actors]]
    /\ \A obligation \in Obligations :
          /\ IF ObligationPropertyClass[obligation] \in {"safety", "evidence"}
                THEN ViolationStates[obligation] =
                         S \ ObligationStates[obligation]
                ELSE TRUE
          /\ ViolatingActions[obligation] =
               ExpectedViolatingActionsFor(
                   obligation, S, ActionLabels, Actions,
                   ObligationPropertyClass,
                   ObligationStates, ViolationStates,
                   AllowedRelationSteps)
    /\ \A claim \in Claims :
          \A obligation \in ClaimObligations[claim] :
              \/ /\ ObligationPropertyClass[obligation] = "liveness"
                     /\ RankedLivenessObligationTyped(
                          S, ActionLabels, Actions,
                          LivenessActiveStates[obligation],
                          LivenessClosedStates[obligation],
                          LivenessProgressActions[obligation],
                          LivenessOtherActions[obligation],
                          LivenessWeakFairProgressActions[obligation],
                          LivenessRankBound[obligation],
                          LivenessRank[obligation],
                          Actors, LivenessFairnessOwner[obligation],
                          LivenessFairnessOwnerOf[obligation])
                 \/ /\ ObligationPropertyClass[obligation] = "relational"
                     /\ AllowedRelationSteps[obligation] # {}
                     /\ \E action \in ActionLabels :
                           \E pair \in Actions[action] :
                               pair \in AllowedRelationSteps[obligation]
                     /\ ViolatingActions[obligation] # {}
                 \/ /\ ObligationPropertyClass[obligation]
                          \in {"safety", "evidence"}
                     /\ \E action \in ViolatingActions[obligation] :
                           RepresentedFalsifier(
                               S, Actions, ObligationStates[obligation],
                               ViolationStates[obligation], action)

SelectedViolatingActionsFor(
        claim, ClaimObligations, ViolatingActions) ==
    UNION {ViolatingActions[obligation] :
              obligation \in ClaimObligations[claim]}

SelectedGovernanceActionsFor(
        claim, ClaimObligations, ObligationPropertyClass,
        ViolatingActions, LivenessProgressActions) ==
    UNION {
        IF ObligationPropertyClass[obligation] = "liveness"
          THEN LivenessProgressActions[obligation]
          ELSE ViolatingActions[obligation] :
        obligation \in ClaimObligations[claim]}

MediatedActionsFor(claim, ClaimActions, PathClassOf) ==
    {action \in ClaimActions[claim] :
        PathClassOf[claim][action] = "mediated"}

ExternalActionsFor(claim, ClaimActions, PathClassOf) ==
    {action \in ClaimActions[claim] :
        PathClassOf[claim][action] = "external"}

BypassActionsFor(claim, ClaimActions, PathClassOf) ==
    {action \in ClaimActions[claim] :
        PathClassOf[claim][action] = "bypass"}

ExcludedActionsFor(claim, ClaimActions, PathClassOf) ==
    {action \in ClaimActions[claim] :
        PathClassOf[claim][action] = "excluded"}

MediationBoundaryTyped(
        S, Claims, Obligations, ActionLabels, Actions,
        ClaimActions, AdmittedActions, ClaimObligations,
        ObligationPropertyClass, ViolatingActions, LivenessProgressActions,
        ObligationRelevantActions, PathClassOf) ==
    /\ ActionFamilyTyped(S, ActionLabels, Actions)
    /\ ClaimActions \in [Claims -> SUBSET ActionLabels]
    /\ AdmittedActions \in [Claims -> SUBSET ActionLabels]
    /\ ClaimObligations \in [Claims -> SUBSET Obligations]
    /\ ObligationPropertyClass \in [Obligations -> PropertyClasses]
    /\ ViolatingActions \in [Obligations -> SUBSET ActionLabels]
    /\ LivenessProgressActions
         \in [Obligations -> SUBSET ActionLabels]
    /\ ObligationRelevantActions \in [Claims -> SUBSET ActionLabels]
    /\ PathClassOf \in [Claims -> [ActionLabels -> MediationPathClasses]]
    /\ \A claim \in Claims :
          /\ SelectedGovernanceActionsFor(
                 claim, ClaimObligations, ObligationPropertyClass,
                 ViolatingActions, LivenessProgressActions)
               \subseteq ClaimActions[claim]
          /\ ObligationRelevantActions[claim] \subseteq ClaimActions[claim]
          /\ AdmittedActions[claim] =
               ClaimActions[claim]
                 \ ExcludedActionsFor(claim, ClaimActions, PathClassOf)
          /\ \A action \in ExcludedActionsFor(
                                claim, ClaimActions, PathClassOf) :
                Actions[action] = {}
          /\ AdmittedActions[claim]
                 \cap SelectedGovernanceActionsFor(
                          claim, ClaimObligations, ObligationPropertyClass,
                          ViolatingActions, LivenessProgressActions)
               \subseteq ObligationRelevantActions[claim]

CompleteMediation(
        claim, ClaimActions, ObligationRelevantActions, PathClassOf) ==
    ObligationRelevantActions[claim]
        \subseteq MediatedActionsFor(claim, ClaimActions, PathClassOf)

AuthorityDependencies(
        claim, ALKAuthority, ActorDependency) ==
    {ActorDependency[actor] : actor \in ALKAuthority[claim]}

AdmittedActionActorsFor(
        claim, AdmittedActions, OwnerOf, DelegateOf) ==
    {OwnerOf[action] : action \in AdmittedActions[claim]}
      \cup UNION {DelegateOf[action] : action \in AdmittedActions[claim]}

AdmittedActionDependenciesFor(
        claim, AdmittedActions, OwnerOf, DelegateOf, ActorDependency) ==
    {ActorDependency[actor] :
        actor \in AdmittedActionActorsFor(
                       claim, AdmittedActions, OwnerOf, DelegateOf)}

ALKAuthorityBoundaryTyped(
        Claims, ActionLabels, Actors, Dependencies,
        ClaimActions, AdmittedActions,
        CommitActions, MediatedActions, ExternalActions,
        PathClassOf,
        OwnerOf, DelegateOf, ALKAuthority,
        ActorDependency, ClaimTCB) ==
    /\ Actors \cap Dependencies = {}
    /\ OwnerOf \in [ActionLabels -> Actors]
    /\ DelegateOf \in [ActionLabels -> SUBSET Actors]
    /\ CommitActions \in [Claims -> SUBSET ActionLabels]
    /\ AdmittedActions \in [Claims -> SUBSET ActionLabels]
    /\ MediatedActions \in [Claims -> SUBSET ActionLabels]
    /\ ExternalActions \in [Claims -> SUBSET ActionLabels]
    /\ PathClassOf \in [Claims -> [ActionLabels -> MediationPathClasses]]
    /\ ALKAuthority \in [Claims -> SUBSET Actors]
    /\ ActorDependency \in [Actors -> Dependencies]
    /\ ClaimTCB \in [Claims -> SUBSET Dependencies]
    /\ \A claim \in Claims :
          /\ ALKAuthority[claim] # {}
          /\ AdmittedActions[claim] \subseteq ClaimActions[claim]
          /\ CommitActions[claim] \subseteq ClaimActions[claim]
          /\ MediatedActions[claim] =
               MediatedActionsFor(claim, ClaimActions, PathClassOf)
          /\ ExternalActions[claim] =
               ExternalActionsFor(claim, ClaimActions, PathClassOf)
          /\ \A action \in MediatedActions[claim] :
                OwnerOf[action] \in ALKAuthority[claim]
          /\ \A action \in ExternalActions[claim] :
                OwnerOf[action] \notin ALKAuthority[claim]
          /\ AuthorityDependencies(claim, ALKAuthority, ActorDependency)
               \subseteq ClaimTCB[claim]
          /\ AdmittedActionDependenciesFor(
                 claim, AdmittedActions, OwnerOf, DelegateOf,
                 ActorDependency) \subseteq ClaimTCB[claim]

FailSafeAdmission(
        S, AdmissionSteps, AuthorizedSourceStates,
        AvailableAuthorizationStates) ==
    /\ RelationTyped(S, AdmissionSteps)
    /\ AuthorizedSourceStates \subseteq S
    /\ AvailableAuthorizationStates \subseteq S
    /\ \A pair \in AdmissionSteps :
          pair[1] \in AuthorizedSourceStates
            \cap AvailableAuthorizationStates

CommitEvidenceBoundaryTyped(
        CommitActions, EvidenceEvents, ObservationDomain,
        Subjects, ActionLabels, Actors, EvidenceClasses,
        EvidenceForCommit, EventObservation, EventSubject,
        EventAction, EventClaimant, EventOwner, EventCommit,
        EventAssurance, EventEvidenceClass) ==
    /\ EvidenceProfileTyped(
           EvidenceEvents, ObservationDomain, Subjects,
           ActionLabels, Actors, CommitActions, EvidenceClasses,
           EventObservation, EventSubject, EventAction,
           EventClaimant, EventOwner, EventCommit,
           EventAssurance, EventEvidenceClass)
    /\ EvidenceForCommit \in [CommitActions -> SUBSET EvidenceEvents]
    /\ \A commit \in CommitActions :
          \A event \in EvidenceForCommit[commit] :
              /\ EventCommit[event] = commit
              /\ EventAction[event] = commit

AtomicCommitEvidenceCoupled(
        RequiredAtCommitActions, EvidenceForCommit,
        EventAssurance) ==
    /\ RequiredAtCommitActions \subseteq DOMAIN EvidenceForCommit
    /\ \A commit \in RequiredAtCommitActions :
          /\ EvidenceForCommit[commit] # {}
          /\ \A event \in EvidenceForCommit[commit] :
                EventAssurance[event] = "at-commit"

EvidenceObligationBoundaryTyped(
        Claims, Subjects, Obligations, ActionLabels, Actors, Providers,
        EvidenceEvents, ClaimCommitActions, EvidenceForCommit,
        ClaimSubject, GuaranteeClaimant, OwnerOf,
        ClaimObligations, ObligationPropertyClass,
        ClaimActions, EvidenceForObligation,
        EventSubject, EventAction, EventClaimant, EventOwner,
        EventCommit, EventAssurance,
        EvidenceProducer, CustodianOf, RetentionProviderOf) ==
    LET CommitActions ==
          UNION {ClaimCommitActions[claim] : claim \in Claims}
    IN
    /\ ClaimSubject \in [Claims -> Subjects]
    /\ GuaranteeClaimant \in [Claims -> Actors]
    /\ OwnerOf \in [ActionLabels -> Actors]
    /\ ClaimObligations \in [Claims -> SUBSET Obligations]
    /\ ObligationPropertyClass \in [Obligations -> PropertyClasses]
    /\ ClaimActions \in [Claims -> SUBSET ActionLabels]
    /\ ClaimCommitActions \in [Claims -> SUBSET ActionLabels]
    /\ EvidenceForCommit \in [CommitActions -> SUBSET EvidenceEvents]
    /\ EvidenceForObligation \in [Obligations -> SUBSET EvidenceEvents]
    /\ EventSubject \in [EvidenceEvents -> Subjects]
    /\ EventAction \in [EvidenceEvents -> ActionLabels]
    /\ EventClaimant \in [EvidenceEvents -> Actors]
    /\ EventOwner \in [EvidenceEvents -> Actors]
    /\ EventCommit \in [EvidenceEvents -> CommitActions]
    /\ EventAssurance \in [EvidenceEvents -> AssurancePositions]
    /\ EvidenceProducer \in [EvidenceEvents -> Actors]
    /\ CustodianOf \in [EvidenceEvents -> Actors]
    /\ RetentionProviderOf \in [EvidenceEvents -> Providers]
    /\ \A claim \in Claims :
          \A obligation \in ClaimObligations[claim] :
              ObligationPropertyClass[obligation] = "evidence"
                => /\ EvidenceForObligation[obligation] # {}
                   /\ \A event \in EvidenceForObligation[obligation] :
                         /\ EventSubject[event] = ClaimSubject[claim]
                         /\ EventClaimant[event] =
                              GuaranteeClaimant[claim]
                         /\ EventAction[event] \in ClaimActions[claim]
                         /\ EventOwner[event] = OwnerOf[EventAction[event]]
                         /\ \E commit \in ClaimCommitActions[claim] :
                               /\ event \in EvidenceForCommit[commit]
                               /\ EventCommit[event] = commit
                               /\ EventAction[event] = commit

GuaranteeFailureBoundaryTyped(
        Claims, ActionLabels, AdvertisedGuaranteeKinds,
        FailureActions, FailureClassOf, GuaranteeUnderFailure) ==
    /\ AdvertisedGuaranteeKinds \in [Claims -> SUBSET GuaranteeKinds]
    /\ FailureActions \in [Claims -> SUBSET ActionLabels]
    /\ FailureClassOf \in [ActionLabels -> ALKFailureClasses]
    /\ GuaranteeUnderFailure
         \in [Claims -> [ALKFailureClasses -> SUBSET GuaranteeKinds]]
    /\ \A claim \in Claims :
          /\ AdvertisedGuaranteeKinds[claim] # {}
          /\ \A failureClass \in ALKFailureClasses :
                GuaranteeUnderFailure[claim][failureClass] # {}

FailureCeilingsRespected(
        Claims, AdvertisedGuaranteeUnderFailure,
        GuaranteeUnderFailure) ==
    \A claim \in Claims, failureClass \in ALKFailureClasses :
        AdvertisedGuaranteeUnderFailure[claim][failureClass]
          \subseteq GuaranteeUnderFailure[claim][failureClass]

CustodyBoundaryTyped(
        ActionLabels, EvidenceEvents, Actors, Providers,
        EvidenceProducer, CustodianOf, RetentionProviderOf,
        CustodyActions, CustodyOwner, CustodyFailureActions) ==
    /\ EvidenceProducer \in [EvidenceEvents -> Actors]
    /\ CustodianOf \in [EvidenceEvents -> Actors]
    /\ RetentionProviderOf \in [EvidenceEvents -> Providers]
    /\ CustodyActions \subseteq ActionLabels
    /\ CustodyOwner \in [CustodyActions -> Actors]
    /\ CustodyFailureActions \subseteq CustodyActions

ClaimSpecificTCBBoundaryTyped(
        Claims, Obligations, ActionLabels, Actors, Dependencies, Providers,
        ClaimTCB, GuaranteeClaimant, ALKAuthority,
        AdmittedActions, ClaimObligations, ObligationPropertyClass,
        OwnerOf, DelegateOf, ActorDependency, ProviderDependency,
        EvidenceEvents, EvidenceForObligation,
        EvidenceProducer, CustodianOf, RetentionProviderOf,
        LivenessFairnessOwner) ==
    /\ ClaimTCB \in [Claims -> SUBSET Dependencies]
    /\ GuaranteeClaimant \in [Claims -> Actors]
    /\ ALKAuthority \in [Claims -> SUBSET Actors]
    /\ AdmittedActions \in [Claims -> SUBSET ActionLabels]
    /\ ClaimObligations \in [Claims -> SUBSET Obligations]
    /\ ObligationPropertyClass \in [Obligations -> PropertyClasses]
    /\ OwnerOf \in [ActionLabels -> Actors]
    /\ DelegateOf \in [ActionLabels -> SUBSET Actors]
    /\ ActorDependency \in [Actors -> Dependencies]
    /\ ProviderDependency \in [Providers -> Dependencies]
    /\ EvidenceForObligation \in [Obligations -> SUBSET EvidenceEvents]
    /\ EvidenceProducer \in [EvidenceEvents -> Actors]
    /\ CustodianOf \in [EvidenceEvents -> Actors]
    /\ RetentionProviderOf \in [EvidenceEvents -> Providers]
    /\ LivenessFairnessOwner \in [Obligations -> Actors]
    /\ \A claim \in Claims :
          LET ClaimEvidenceEvents ==
                UNION {
                    IF ObligationPropertyClass[obligation] = "evidence"
                      THEN EvidenceForObligation[obligation]
                      ELSE {} :
                    obligation \in ClaimObligations[claim]}
              RequiredActors ==
                {GuaranteeClaimant[claim]}
                  \cup ALKAuthority[claim]
                  \cup AdmittedActionActorsFor(
                          claim, AdmittedActions, OwnerOf, DelegateOf)
                  \cup {EvidenceProducer[event] :
                          event \in ClaimEvidenceEvents}
                  \cup {CustodianOf[event] :
                          event \in ClaimEvidenceEvents}
                  \cup {LivenessFairnessOwner[obligation] :
                          obligation \in
                            {selected \in ClaimObligations[claim] :
                                ObligationPropertyClass[selected]
                                  = "liveness"}}
              RequiredProviders ==
                {RetentionProviderOf[event] :
                    event \in ClaimEvidenceEvents}
          IN  /\ {ActorDependency[actor] : actor \in RequiredActors}
                    \subseteq ClaimTCB[claim]
              /\ {ProviderDependency[provider] :
                       provider \in RequiredProviders}
                    \subseteq ClaimTCB[claim]

RelyDischargeBoundaryTyped(
        S, Components, RelyEdges, RelyRank, RelyPropertyClassOf,
        DirectMutualClosureEdges,
        ComponentObligationStates,
        ComponentRelySteps, ComponentGuaranteeSteps,
        SharedStepsForRelyEdge) ==
    /\ RelyEdges \subseteq Components \X Components
    /\ RelyRank \in [Components -> Nat]
    /\ RelyPropertyClassOf \in [RelyEdges -> PropertyClasses]
    /\ DirectMutualClosureEdges \subseteq RelyEdges
    /\ ComponentObligationStates \in [Components -> SUBSET S]
    /\ ComponentRelySteps \in [Components -> SUBSET Pairs(S)]
    /\ ComponentGuaranteeSteps \in [Components -> SUBSET Pairs(S)]
    /\ SharedStepsForRelyEdge
         \in [Components \X Components -> SUBSET Pairs(S)]
    /\ \A component \in Components :
          ComponentObligationStates[component] # {}
    /\ \A edge \in RelyEdges :
          /\ ComponentGuaranteeSteps[edge[2]] # {}
          /\ ComponentGuaranteeSteps[edge[2]]
               \subseteq ComponentRelySteps[edge[1]]
    /\ \A component \in Components :
          <<component, component>> \notin RelyEdges
    /\ \A edge \in DirectMutualClosureEdges :
          /\ RelyPropertyClassOf[edge] = "safety"
          /\ <<edge[2], edge[1]>> \in DirectMutualClosureEdges
          /\ SharedStepsForRelyEdge[edge] # {}
          /\ SharedStepsForRelyEdge[edge] =
               SharedStepsForRelyEdge[<<edge[2], edge[1]>>]
          /\ Stable(
                 S, ComponentObligationStates[edge[1]],
                 SharedStepsForRelyEdge[edge])
          /\ Stable(
                 S, ComponentObligationStates[edge[2]],
                 SharedStepsForRelyEdge[edge])
    /\ \A edge \in RelyEdges :
          \/ RelyRank[edge[2]] < RelyRank[edge[1]]
          \/ edge \in DirectMutualClosureEdges

DistributedProfileBoundaryTyped(
        S, Actors, Epochs, MembershipOf, EpochOf,
        AllowedDecisionSets, CollectiveCommitSteps,
        CommitDecisionMembers, CommitEpoch,
        PartitionedStates, ReconfigurationSteps,
        RetrySteps, RecoverySteps) ==
    /\ S # {}
    /\ Actors # {}
    /\ Epochs # {}
    /\ MembershipOf \in [S -> SUBSET Actors]
    /\ EpochOf \in [S -> Epochs]
    /\ AllowedDecisionSets \in [S -> SUBSET (SUBSET Actors)]
    /\ RelationTyped(S, CollectiveCommitSteps)
    /\ RelationTyped(S, ReconfigurationSteps)
    /\ RelationTyped(S, RetrySteps)
    /\ RelationTyped(S, RecoverySteps)
    /\ PartitionedStates \subseteq S
    /\ CommitDecisionMembers
         \in [CollectiveCommitSteps -> SUBSET Actors]
    /\ CommitEpoch \in [CollectiveCommitSteps -> Epochs]
    /\ \A state \in S :
          /\ MembershipOf[state] # {}
          /\ \A decisionSet \in AllowedDecisionSets[state] :
                /\ decisionSet # {}
                /\ decisionSet \subseteq MembershipOf[state]
    /\ \A pair \in CollectiveCommitSteps :
          /\ CommitDecisionMembers[pair]
               \in AllowedDecisionSets[pair[1]]
          /\ CommitEpoch[pair] = EpochOf[pair[1]]
          /\ EpochOf[pair[2]] = EpochOf[pair[1]]
    /\ \A pair \in ReconfigurationSteps :
          EpochOf[pair[2]] # EpochOf[pair[1]]

ObservationResidualBoundaryTyped(
        S, Claims, ActionLabels, Actors, ObservationValues,
        ClaimActions, ALKAuthority, OwnerOf, Observe,
        ObservationCeiling, ResidualActions,
        ResidualClassOf, ResidualGuaranteeCeiling) ==
    /\ Observe \in [Claims -> [S -> ObservationValues]]
    /\ ObservationCeiling
         \in [Claims -> SUBSET ObservationDimensions]
    /\ ResidualActions \in [Claims -> SUBSET ActionLabels]
    /\ ResidualClassOf \in [ActionLabels -> ResidualClasses]
    /\ ResidualGuaranteeCeiling
         \in [Claims -> [ActionLabels -> SUBSET GuaranteeKinds]]
    /\ \A claim \in Claims :
          /\ ResidualActions[claim] \subseteq ClaimActions[claim]
          /\ \A action \in ResidualActions[claim] :
                /\ OwnerOf[action] \in Actors \ ALKAuthority[claim]
                /\ ResidualGuaranteeCeiling[claim][action] # {}

ALKClaimBoundaryCoherent(
        Claims, ClaimActions, AdmittedActions,
        ObligationRelevantActions, ExternalActions,
        CommitActions, FailureActions, ResidualActions) ==
    \A claim \in Claims :
        /\ AdmittedActions[claim] \subseteq ClaimActions[claim]
        /\ ObligationRelevantActions[claim] \subseteq AdmittedActions[claim]
        /\ ExternalActions[claim] = ResidualActions[claim]
        /\ CommitActions[claim] \subseteq ObligationRelevantActions[claim]
        /\ CommitActions[claim] \subseteq AdmittedActions[claim]
        /\ FailureActions[claim] \subseteq ClaimActions[claim]
        /\ ResidualActions[claim] \subseteq AdmittedActions[claim]

====
