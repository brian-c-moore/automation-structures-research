---- MODULE ALKProfilesWitness ----
EXTENDS ALKConstructionTheoremWitness, ALKProfiles, FiniteSets

ProfileStates == {"open", "reconfigured", "closed", "failed"}
ProfileSafeStates == {"open", "reconfigured", "closed"}
ProfileActionLabels ==
    {"commit", "fault", "shared", "external", "bypass",
     "reconfigure", "retry", "recover"}

ProfilePotentialActions ==
    [action \in ProfileActionLabels |->
        CASE action = "commit" ->
               {<<"open", "closed">>, <<"reconfigured", "closed">>}
          [] action = "fault" ->
               {<<"open", "failed">>, <<"reconfigured", "failed">>}
          [] action = "shared" ->
               {<<"open", "open">>,
                <<"reconfigured", "reconfigured">>}
          [] action = "external" -> {<<"closed", "closed">>}
          [] action = "reconfigure" -> {<<"open", "reconfigured">>}
          [] action = "retry" -> {<<"reconfigured", "reconfigured">>}
          [] action = "recover" -> {<<"failed", "reconfigured">>}
          [] OTHER -> {}]

ProfilePostMediationSteps(profile) ==
    [action \in ProfileActionLabels |->
        CASE action = "commit" ->
               IF profile = "bounded-distributed"
                 THEN {<<"reconfigured", "closed">>}
                 ELSE {<<"open", "closed">>}
          [] action = "shared" ->
               IF profile = "bounded-distributed"
                 THEN {<<"reconfigured", "reconfigured">>}
                 ELSE {<<"open", "open">>}
          [] action = "external" -> {<<"closed", "closed">>}
          [] action = "reconfigure" ->
               IF profile = "bounded-distributed"
                 THEN {<<"open", "reconfigured">>}
                 ELSE {}
          [] action = "retry" ->
               IF profile = "bounded-distributed"
                 THEN {<<"reconfigured", "reconfigured">>}
                 ELSE {}
          [] action = "recover" ->
               IF profile = "bounded-distributed"
                 THEN {<<"failed", "reconfigured">>}
                 ELSE {}
          [] OTHER -> {}]

ProfileClaims(profile) == {profile}
ExactProfileRegistryHeld ==
    ProfileNames =
      {"local-reference", "modular", "delegated", "bounded-distributed"}
ProfileSubjects == {"work"}
ProfileActors ==
    {"builder", "custodian", "assurer", "external-owner",
     "cluster-owner", "node-a", "node-b", "node-c"}
ProfileProviders == {"assurer", "audit-provider"}

ProfileSelectedStructures(profile) == ExpectedProfileStructures(profile)
ProfileSelectedExecutionModality(profile) ==
    ExpectedProfileExecutionModality(profile)
ProfileSelectedStructuresForClaim(profile) ==
    [claim \in ProfileClaims(profile) |->
        ProfileSelectedStructures(profile)]
ProfileCompositionSeamObligationOccurrences(profile) ==
    [claim \in ProfileClaims(profile) |-> {}]
ProfileClaimObligationOccurrences(profile) ==
    [claim \in ProfileClaims(profile) |->
        RequiredALKObligationOccurrences(
            ProfileSelectedStructures(profile),
            ProfileSelectedExecutionModality(profile),
            StructureObligationOccurrences,
            ExecutionModalityObligationOccurrences,
            ProfileCompositionSeamObligationOccurrences(profile)[claim])]
ProfileClaimObligations(profile) ==
    [claim \in ProfileClaims(profile) |->
        RequiredALKObligations(
            ProfileSelectedStructures(profile),
            ProfileSelectedExecutionModality(profile),
            StructureObligationOccurrences,
            ExecutionModalityObligationOccurrences,
            ProfileCompositionSeamObligationOccurrences(profile)[claim],
            NormalizedKeyOf)]

ProfileObligationStates ==
    [obligation \in Obligations |->
        IF ObligationPropertyClass[obligation] = "liveness"
          THEN ProfileStates
          ELSE ProfileSafeStates]
ProfileViolationStates ==
    [obligation \in Obligations |->
        ProfileStates \ ProfileObligationStates[obligation]]
ProfileAllowedRelationSteps ==
    [obligation \in Obligations |-> Pairs(ProfileStates)]
ProfileViolatingActions ==
    [obligation \in Obligations |->
        ExpectedViolatingActionsFor(
            obligation, ProfileStates, ProfileActionLabels,
            ProfilePotentialActions, ObligationPropertyClass,
            ProfileObligationStates, ProfileViolationStates,
            ProfileAllowedRelationSteps)]
ProfileDerivedFrom == [obligation \in Obligations |-> {}]
ProfileLivenessActiveStates ==
    [obligation \in Obligations |-> {"open", "reconfigured"}]
ProfileLivenessClosedStates ==
    [obligation \in Obligations |-> {"closed", "failed"}]
ProfileLivenessProgressActions ==
    [obligation \in Obligations |-> {"commit"}]
ProfileLivenessOtherActions ==
    [obligation \in Obligations |-> ProfileActionLabels \ {"commit"}]
ProfileLivenessWeakFairProgressActions ==
    [obligation \in Obligations |-> {"commit"}]
ProfileLivenessRankBound == [obligation \in Obligations |-> 1]
ProfileLivenessRank ==
    [obligation \in Obligations |->
        [state \in ProfileStates |->
            IF state \in {"open", "reconfigured", "failed"}
              THEN 1
              ELSE 0]]
ProfileLivenessFairnessOwner(profile) ==
    [obligation \in Obligations |-> ExpectedProfileCommitOwner(profile)]
ProfileLivenessFairnessOwnerOf(profile) ==
    [obligation \in Obligations |->
        [action \in ProfileActionLabels |->
            ExpectedProfileCommitOwner(profile)]]

ProfileClaimActions(profile) ==
    [claim \in ProfileClaims(profile) |-> ProfileActionLabels]
ProfileAdmittedActions(profile) ==
    [claim \in ProfileClaims(profile) |->
        ProfileActionLabels \ {"bypass"}]
ProfilePathClassOf(profile) ==
    [claim \in ProfileClaims(profile) |->
        [action \in ProfileActionLabels |->
            IF action = "bypass"
              THEN "excluded"
              ELSE IF action = "external"
                THEN "external"
                ELSE "mediated"]]
ProfileGovernedCommitSteps(profile) ==
    ProfilePostMediationSteps(profile)["commit"]
ProfileClaimCommitActions(profile) ==
    [claim \in ProfileClaims(profile) |-> {"commit"}]
ProfileGovernedActions(profile) ==
    [claim \in ProfileClaims(profile) |->
        DerivedGovernedActionsFor(
            claim, ProfileClaimObligations(profile),
            ObligationPropertyClass, ProfileViolatingActions,
            ProfileLivenessProgressActions,
            ProfileClaimCommitActions(profile),
            ProfileAdmittedActions(profile))]
ProfileObligationRelevantActions(profile) ==
    ProfileGovernedActions(profile)
ProfileOwnerOf(profile) ==
    [action \in ProfileActionLabels |->
        IF action = "external"
          THEN "custodian"
          ELSE IF action = "commit"
            THEN ExpectedProfileCommitOwner(profile)
            ELSE IF profile = "bounded-distributed"
                    /\ action \in {"reconfigure", "retry", "recover"}
              THEN "cluster-owner"
              ELSE "builder"]
ProfileDelegateOf == [action \in ProfileActionLabels |-> {}]
ProfileALKAuthority(profile) ==
    [claim \in ProfileClaims(profile) |->
        {"builder", ExpectedProfileCommitOwner(profile)}]
ProfileFormalStepsForClaim(profile) ==
    [claim \in ProfileClaims(profile) |->
        ActionUnion(
            ProfileAdmittedActions(profile)[claim],
            ProfilePostMediationSteps(profile))]

ProfileClaimSubject(profile) ==
    [claim \in ProfileClaims(profile) |-> "work"]
ProfileGuaranteeClaimant(profile) ==
    [claim \in ProfileClaims(profile) |-> "builder"]
ProfileAssuranceProviderOf ==
    [action \in ProfileActionLabels |-> "assurer"]
ProfileAssurancePositionOf ==
    [action \in ProfileActionLabels |-> "at-commit"]
ProfilePreventionControllers == {"assurer"}
ProfileUnavailableProviders == {}
ProfilePersistentEvidenceFor ==
    [action \in ProfileActionLabels |-> TRUE]
ProfileRecoveryAvailableFor ==
    [action \in ProfileActionLabels |-> TRUE]

ProfileALKCommitEvent(profile) ==
    IF profile = "bounded-distributed"
      THEN "reconfigured-commit-event"
      ELSE "open-commit-event"
ProfileKernelCommitEvent(profile) ==
    IF profile = "bounded-distributed"
      THEN "kernel-reconfigured-commit-event"
      ELSE "kernel-open-commit-event"
ProfileEvidenceEvents(profile) == {ProfileALKCommitEvent(profile)}
ProfileKernelEvidenceEvents(profile) == {ProfileKernelCommitEvent(profile)}
ProfileEvidenceRequiredActions(profile) ==
    [claim \in ProfileClaims(profile) |-> {"commit"}]
ProfileEvidenceForCommit(profile) ==
    [action \in {"commit"} |-> ProfileEvidenceEvents(profile)]
ProfileEventSubject(profile) ==
    [event \in ProfileEvidenceEvents(profile) |-> "work"]
ProfileEventAction(profile) ==
    [event \in ProfileEvidenceEvents(profile) |-> "commit"]
ProfileEventClaimant(profile) ==
    [event \in ProfileEvidenceEvents(profile) |-> "builder"]
ProfileEventOwner(profile) ==
    [event \in ProfileEvidenceEvents(profile) |->
        ExpectedProfileCommitOwner(profile)]
ProfileEventCommit(profile) ==
    [event \in ProfileEvidenceEvents(profile) |-> "commit"]
ProfileEventAssurance(profile) ==
    [event \in ProfileEvidenceEvents(profile) |-> "at-commit"]
ProfileEventObservation(profile) ==
    [event \in ProfileEvidenceEvents(profile) |-> "closed-view"]
ProfileEventEvidenceClass(profile) ==
    [event \in ProfileEvidenceEvents(profile) |-> "evidence"]
ProfileEvidenceProducer(profile) ==
    [event \in ProfileEvidenceEvents(profile) |->
        ExpectedProfileCommitOwner(profile)]
ProfileCustodianOf(profile) ==
    [event \in ProfileEvidenceEvents(profile) |-> "custodian"]
ProfileRetentionProviderOf(profile) ==
    [event \in ProfileEvidenceEvents(profile) |-> "audit-provider"]
ProfileEvidenceKernelEvent(profile) ==
    [event \in ProfileEvidenceEvents(profile) |->
        ProfileKernelCommitEvent(profile)]

ProfileComponents == CompositionComponents
ProfileProcessBoundaries(profile) ==
    ExpectedProfileProcessBoundaries(profile)
ProfileProcessOwner(profile) ==
    ExpectedProfileProcessOwner(profile)
ProfileComponentPlacement(profile) ==
    ExpectedProfileComponentPlacement(profile)
ProfileTopologyBoundaryHeld(profile) ==
    ProfileTopologyBoundaryTyped(
        profile, ProfileActors, ProfileProcessBoundaries(profile),
        ProfileProcessOwner(profile), ProfileComponentPlacement(profile),
        ExpectedProfileCommitOwner(profile))
ProfileRelyEdges(profile) ==
    IF profile = "modular"
      THEN PossibleRelyEdges
      ELSE {<<"component-a", "component-b">>}
ProfileRelyRank(profile) ==
    [component \in ProfileComponents |->
        IF profile = "modular"
          THEN 0
          ELSE IF component = "component-a" THEN 1 ELSE 0]
ProfileRelyPropertyClassOf(profile) ==
    [edge \in ProfileRelyEdges(profile) |-> "safety"]
ProfileDirectMutualClosureEdges(profile) ==
    IF profile = "modular" THEN PossibleRelyEdges ELSE {}
ProfileComponentObligationStates ==
    [component \in ProfileComponents |-> ProfileSafeStates]
ProfileCompositionStepA(profile) ==
    ProfileFormalStepsForClaim(profile)[profile]
      \ (ProfilePostMediationSteps(profile)["external"]
           \cup ProfilePostMediationSteps(profile)["shared"])
ProfileCompositionStepB(profile) ==
    ProfilePostMediationSteps(profile)["external"]
ProfileRegisteredSharedSteps(profile) ==
    ProfilePostMediationSteps(profile)["shared"]
ProfileComponentRelySteps(profile) ==
    [component \in ProfileComponents |->
        IF component = "component-a"
          THEN ProfileCompositionStepB(profile)
          ELSE IF profile = "modular"
            THEN ProfileCompositionStepA(profile)
            ELSE {}]
ProfileComponentGuaranteeSteps(profile) ==
    [component \in ProfileComponents |->
        IF component = "component-a"
          THEN ProfileCompositionStepA(profile)
          ELSE ProfileCompositionStepB(profile)]
ProfileSharedStepsForRelyEdge(profile) ==
    [edge \in ProfileComponents \X ProfileComponents |->
        ProfileRegisteredSharedSteps(profile)]
ProfileRepresentedSharedSteps(profile) ==
    ProfileRegisteredSharedSteps(profile)
ProfileAffectedComponents == ProfileComponents

ProfileActorDependency ==
    [actor \in ProfileActors |->
        IF actor = "custodian" THEN "audit-store" ELSE "kernel-code"]
ProfileProviderDependency ==
    [provider \in ProfileProviders |->
        IF provider = "audit-provider"
          THEN "audit-store"
          ELSE "kernel-code"]
ProfileClaimTCB(profile) ==
    [claim \in ProfileClaims(profile) |-> Dependencies]

ProfileRetainedStructuresForKernel ==
    RetainedStructureNames \cup RetainedExecutionModalityNames
ProfileSelectedStructuresForKernel(profile) ==
    ProfileSelectedStructures(profile)
      \cup {ProfileSelectedExecutionModality(profile)}
ProfileSelectedExecutionCarrier(profile) ==
    ProfileSelectedExecutionModality(profile)
ProfileInstances(profile) ==
    ProfileSelectedStructuresForKernel(profile)
ProfileStructureOf(profile) ==
    [instance \in ProfileInstances(profile) |-> instance]
ProfileParameterDomain == {"bounded-parameter"}
ProfileParameterDomainOf(profile) ==
    [structure \in ProfileSelectedStructuresForKernel(profile) |->
        ProfileParameterDomain]
ProfileParameters(profile) ==
    [instance \in ProfileInstances(profile) |-> "bounded-parameter"]

ProfileSelectedFamilies == SelectedFamilies
ProfileDeclaredGlobalAssumptions == DeclaredGlobalAssumptions
ProfileLibraryPremises == LibraryPremises
ProfileDeploymentPremises == DeploymentPremises
ProfileDischargedPremises == DischargedPremises

ProfileRegisteredGuarantees ==
    RegisteredGuarantees \cup {"recovery-result"}
ProfileGuaranteeFamily ==
    [guarantee \in ProfileRegisteredGuarantees |->
        IF guarantee = "recovery-result"
          THEN "ownership-assurance"
          ELSE GuaranteeFamily[guarantee]]
ProfileGuaranteeKindOf ==
    [guarantee \in ProfileRegisteredGuarantees |->
        IF guarantee = "recovery-result"
          THEN "recovery"
          ELSE GuaranteeKindOf[guarantee]]
ProfileGuaranteePropertyClass ==
    [guarantee \in ProfileRegisteredGuarantees |->
        IF guarantee = "recovery-result"
          THEN "safety"
          ELSE GuaranteePropertyClass[guarantee]]
ProfileGuaranteeObligations(profile) ==
    [guarantee \in ProfileRegisteredGuarantees |->
        IF ProfileGuaranteeFamily[guarantee]
             \in {"obligation", "progress", "refinement"}
          THEN {obligation \in ProfileClaimObligations(profile)[profile] :
                    KernelGuaranteeObligationClassCompatible(
                        ProfileGuaranteePropertyClass[guarantee],
                        ObligationPropertyClass[obligation])}
          ELSE {}]

ProfileFormalStates == ProfileStates
ProfileImplementationStates == ProfileStates
ProfileFormalInitial == {"open"}
ProfileImplementationInitial == ProfileFormalInitial
ProfileFormalSteps(profile) ==
    ProfileFormalStepsForClaim(profile)[profile]
ProfileImplementationSteps(profile) == ProfileFormalSteps(profile)
ProfileFormalCommitSteps(profile) ==
    ProfileGovernedCommitSteps(profile)
ProfileImplementationCommitSteps(profile) ==
    ProfileFormalCommitSteps(profile)
ProfileFormalFailureSteps == {}
ProfileImplementationFailureSteps == {}
ProfileFormalEnvironmentSteps(profile) ==
    ProfilePostMediationSteps(profile)["external"]
ProfileDeploymentSteps(profile) ==
    ProfileFormalEnvironmentSteps(profile)
ProfileTrustedSteps(profile) ==
    ProfileFormalSteps(profile) \ ProfileFormalEnvironmentSteps(profile)
ProfileObservationDomain ==
    {"open-view", "reconfigured-view", "closed-view", "failed-view"}
ProfileAbstraction == [state \in ProfileStates |-> state]
ProfileFormalObserve ==
    [state \in ProfileStates |->
        CASE state = "open" -> "open-view"
          [] state = "reconfigured" -> "reconfigured-view"
          [] state = "closed" -> "closed-view"
          [] OTHER -> "failed-view"]
ProfileImplementationObserve == ProfileFormalObserve
ProfileFormalPersistentObserve ==
    [state \in ProfileStates |-> state \in ProfileSafeStates]
ProfileImplementationPersistentObserve ==
    ProfileFormalPersistentObserve
ProfileImplementationCommitOwner(profile) ==
    [step \in ProfileImplementationCommitSteps(profile) |->
        ExpectedProfileCommitOwner(profile)]
ProfileFormalCommitOwner(profile) ==
    [step \in ProfileFormalCommitSteps(profile) |->
        ExpectedProfileCommitOwner(profile)]
ProfileImplementationCommitDelegate(profile) ==
    [step \in ProfileImplementationCommitSteps(profile) |->
        ExpectedProfileCommitOwner(profile)]
ProfileFormalCommitDelegate(profile) ==
    [step \in ProfileFormalCommitSteps(profile) |->
        ExpectedProfileCommitOwner(profile)]
ProfileImplementationCommitAssurance(profile) ==
    [step \in ProfileImplementationCommitSteps(profile) |-> "at-commit"]
ProfileFormalCommitAssurance(profile) ==
    [step \in ProfileFormalCommitSteps(profile) |-> "at-commit"]

ProfileDeclaredBoundary(profile) ==
    ConstructionBoundaryId(
        ProfileFormalStates, ProfileFormalCommitSteps(profile),
        ProfileFormalObserve)
ProfileDeclaredFailureCeiling(profile) ==
    ConstructionFailureCeilingId(ProfileFormalFailureSteps, {})
ProfileBoundaryIds(profile) == {ProfileDeclaredBoundary(profile)}
ProfileFailureCeilings(profile) ==
    {ProfileDeclaredFailureCeiling(profile)}
ProfileGuaranteeBoundaryOf(profile) ==
    [guarantee \in ProfileRegisteredGuarantees |->
        ProfileDeclaredBoundary(profile)]
ProfileGuaranteeFailureCeilingOf(profile) ==
    [guarantee \in ProfileRegisteredGuarantees |->
        ProfileDeclaredFailureCeiling(profile)]

ProfileKernelActors(profile) ==
    {"builder", ExpectedProfileCommitOwner(profile), "assurer"}
ProfileKernelProviders == {"assurer"}
ProfileKernelClaimant == "builder"
ProfileKernelCommitOwner(profile) == ExpectedProfileCommitOwner(profile)
ProfileKernelCommitDelegate(profile) == ExpectedProfileCommitOwner(profile)
ProfileKernelAssuranceProvider == "assurer"
ProfileKernelAssurancePosition == "at-commit"
ProfileKernelPreventionControllers == {"assurer"}
ProfileKernelUnavailableProviders == {}
ProfileKernelPersistentEvidence == TRUE
ProfileKernelRecoveryAvailable == TRUE
ProfileKernelCheckActMode == "atomic"
ProfileKernelCheckResultStates == {"open", "reconfigured"}
ProfileKernelPredicateStates == ProfileSafeStates
ProfileKernelInterferenceSteps(profile) ==
    ProfileFormalSteps(profile) \ ProfileFormalCommitSteps(profile)
ProfileKernelGovernedCommitSteps(profile) ==
    ProfileFormalCommitSteps(profile)
ProfileObligationSystemSteps(profile) ==
    ProfileFormalSteps(profile) \ ProfileFormalEnvironmentSteps(profile)
ProfileObligationEnvironmentSteps(profile) ==
    ProfileFormalEnvironmentSteps(profile)
ProfileObligationRelySteps(profile) ==
    ProfileFormalEnvironmentSteps(profile)

ProfileObligationFamilyPremises(profile) ==
    ObligationPreservationPremises(
        ProfileStates, ProfileFormalInitial, ProfileSafeStates,
        ProfileObligationSystemSteps(profile),
        ProfileObligationEnvironmentSteps(profile),
        ProfileObligationRelySteps(profile))
ProfileObligationFamilyConclusion(profile) ==
    ObligationPreservationConclusion(
        ProfileStates, ProfileFormalInitial, ProfileSafeStates,
        ProfileObligationSystemSteps(profile),
        ProfileObligationEnvironmentSteps(profile))
ProfileCheckActFamilyPremises(profile) ==
    CheckActAdmission(
        ProfileStates, ProfileKernelCheckActMode,
        ProfileKernelCheckResultStates, ProfileKernelPredicateStates,
        ProfileKernelInterferenceSteps(profile),
        ProfileKernelGovernedCommitSteps(profile))
ProfileCheckActFamilyConclusion(profile) ==
    CheckActLicensed(
        ProfileStates, ProfileKernelPredicateStates,
        ProfileKernelGovernedCommitSteps(profile))
ProfileOwnershipAssuranceFamilyPremises(profile) ==
    AssuranceBoundaryTyped(
        ProfileStates, ProfileKernelActors(profile),
        ProfileKernelProviders, ProfileKernelClaimant,
        ProfileKernelCommitOwner(profile),
        ProfileKernelCommitDelegate(profile),
        ProfileKernelAssuranceProvider,
        ProfileKernelAssurancePosition,
        ProfileKernelPreventionControllers,
        ProfileFormalFailureSteps,
        ProfileKernelUnavailableProviders,
        ProfileFormalPersistentObserve,
        ProfileKernelPersistentEvidence,
        ProfileKernelRecoveryAvailable)
ProfileOwnershipAssuranceFamilyConclusion(profile) ==
    OwnershipAssuranceCeiling(
        ProfileKernelClaimant, ProfileKernelCommitOwner(profile),
        ProfileKernelAssuranceProvider,
        ProfileKernelAssurancePosition,
        ProfileKernelPreventionControllers,
        ProfileKernelUnavailableProviders,
        ProfileKernelPersistentEvidence,
        ProfileKernelRecoveryAvailable)
ProfileSupportedGuaranteeKinds(profile) ==
    GuaranteeCeiling(
        ProfileKernelClaimant, ProfileKernelCommitOwner(profile),
        ProfileKernelAssuranceProvider,
        ProfileKernelAssurancePosition,
        ProfileKernelPreventionControllers,
        ProfileKernelUnavailableProviders,
        ProfileKernelPersistentEvidence,
        ProfileKernelRecoveryAvailable)

ProfileCompositionInitialStates == ProfileFormalInitial
ProfileCompositionInvA == ProfileSafeStates
ProfileCompositionInvB == ProfileSafeStates
ProfileCompositionSharedSteps(profile) ==
    ProfileRegisteredSharedSteps(profile)
ProfileCompositionEnvironmentSteps(profile) ==
    ProfileFormalEnvironmentSteps(profile)
ProfileCompositionFailureSteps == ProfileFormalFailureSteps
ProfileCompositionInterferenceSteps(profile) ==
    ProfileCompositionSharedSteps(profile)
      \cup ProfileCompositionEnvironmentSteps(profile)
ProfileCompositionRelyA(profile) ==
    ProfileCompositionStepB(profile)
ProfileCompositionRelyB(profile) ==
    IF profile = "modular"
      THEN ProfileCompositionStepA(profile)
      ELSE {}
ProfileCompositionFamilyPremises(profile) ==
    CompositionSafetyPremises(
        ProfileStates, ProfileCompositionInitialStates,
        ProfileCompositionInvA, ProfileCompositionInvB,
        ProfileCompositionStepA(profile),
        ProfileCompositionStepB(profile),
        ProfileCompositionSharedSteps(profile),
        ProfileCompositionEnvironmentSteps(profile),
        ProfileCompositionFailureSteps,
        ProfileCompositionInterferenceSteps(profile),
        ProfileCompositionRelyA(profile),
        ProfileCompositionRelyB(profile),
        ProfileRelyEdges(profile), ProfileKernelProviders, {})
ProfileCompositionFamilyConclusion(profile) ==
    CompositionSafetyConclusion(
        ProfileStates, ProfileCompositionInitialStates,
        ProfileCompositionInvA, ProfileCompositionInvB,
        ProfileCompositionStepA(profile),
        ProfileCompositionStepB(profile),
        ProfileCompositionSharedSteps(profile),
        ProfileCompositionEnvironmentSteps(profile),
        ProfileCompositionFailureSteps,
        ProfileCompositionInterferenceSteps(profile))

ProfileSelectedClasses == SelectedClasses
ProfileFormalSafeStates == ProfileSafeStates
ProfileFormalObservationStates == ProfileSafeStates
ProfileAllowedObservations ==
    {"open-view", "reconfigured-view", "closed-view"}
ProfileFormalClosedStates == {"closed"}
ProfileImplementationClosedStates == {"closed"}
ProfileImplementationActiveStates ==
    ProfileStates \ ProfileImplementationClosedStates
ProfileFormalProgressSteps(profile) ==
    ProfileFormalCommitSteps(profile)
ProfileImplementationProgressSteps(profile) ==
    ProfileFormalProgressSteps(profile)
ProfileFormalOtherSteps(profile) ==
    ProfileFormalSteps(profile) \ ProfileFormalProgressSteps(profile)
ProfileImplementationOtherSteps(profile) ==
    ProfileFormalOtherSteps(profile)
ProfileRankBound == 1
ProfileFormalRank ==
    [state \in ProfileStates |->
        IF state = "closed" THEN 0 ELSE 1]
ProfileImplementationRank == ProfileFormalRank
ProfileFairnessOwners(profile) == {ExpectedProfileCommitOwner(profile)}
ProfileFairnessOwner(profile) == ExpectedProfileCommitOwner(profile)
ProfileFormalFairnessOwnerOf(profile) ==
    [step \in ProfileFormalProgressSteps(profile) |->
        ExpectedProfileCommitOwner(profile)]
ProfileImplementationFairnessOwnerOf(profile) ==
    [step \in ProfileImplementationProgressSteps(profile) |->
        ExpectedProfileCommitOwner(profile)]
ProfileRefinementFamilyPremises(profile) ==
    RefinementTransferPremises(
        ProfileSelectedClasses,
        ProfileImplementationStates, ProfileImplementationActiveStates,
        ProfileImplementationClosedStates, ProfileFormalStates,
        ProfileImplementationInitial, ProfileFormalInitial,
        ProfileImplementationSteps(profile), ProfileFormalSteps(profile),
        ProfileFormalSafeStates, ProfileFormalObservationStates,
        ProfileObservationDomain, ProfileAllowedObservations,
        ProfileAbstraction, ProfileImplementationObserve,
        ProfileFormalObserve, ProfileFormalClosedStates,
        ProfileFormalProgressSteps(profile), ProfileFormalOtherSteps(profile),
        ProfileImplementationProgressSteps(profile),
        ProfileImplementationOtherSteps(profile),
        ProfileRankBound, ProfileFormalRank, ProfileImplementationRank,
        ProfileFairnessOwners(profile), ProfileFairnessOwner(profile),
        ProfileFormalFairnessOwnerOf(profile),
        ProfileImplementationFairnessOwnerOf(profile))
ProfileRefinementFamilyConclusion(profile) ==
    RefinementTransferConclusion(
        ProfileSelectedClasses,
        ProfileImplementationStates, ProfileImplementationClosedStates,
        ProfileImplementationInitial, ProfileImplementationSteps(profile),
        ProfileFormalSafeStates, ProfileFormalObservationStates,
        ProfileAllowedObservations, ProfileAbstraction,
        ProfileImplementationObserve)
ProfileSafetyRefinementPremisesHeld(profile) ==
    SafetyRefinementPremises(
        ProfileImplementationStates, ProfileFormalStates,
        ProfileImplementationInitial, ProfileFormalInitial,
        ProfileImplementationSteps(profile), ProfileFormalSteps(profile),
        ProfileFormalSafeStates, ProfileObservationDomain,
        ProfileAbstraction, ProfileImplementationObserve,
        ProfileFormalObserve)
ProfileObservationRefinementPremisesHeld ==
    ObservationPropertyPremises(
        ProfileImplementationStates, ProfileFormalStates,
        ProfileFormalObservationStates, ProfileObservationDomain,
        ProfileAllowedObservations, ProfileAbstraction,
        ProfileImplementationObserve, ProfileFormalObserve)
ProfileSafetyRefinementConclusionHeld(profile) ==
    SafetyRefinementConclusion(
        ProfileImplementationStates, ProfileImplementationInitial,
        ProfileImplementationSteps(profile), ProfileFormalSafeStates,
        ProfileAbstraction)
ProfileObservationRefinementConclusionHeld ==
    ObservationPropertyConclusion(
        ProfileImplementationStates, ProfileFormalObservationStates,
        ProfileAllowedObservations, ProfileAbstraction,
        ProfileImplementationObserve)

ProfileKernelEvidenceSubjects == {"work"}
ProfileKernelEvidenceCommitActionLinks(profile) ==
    {<<step, step>> : step \in ProfileFormalCommitSteps(profile)}
ProfileKernelEventObservation(profile) ==
    [event \in ProfileKernelEvidenceEvents(profile) |-> "closed-view"]
ProfileKernelEventSubject(profile) ==
    [event \in ProfileKernelEvidenceEvents(profile) |-> "work"]
ProfileKernelEventAction(profile) ==
    [event \in ProfileKernelEvidenceEvents(profile) |->
        CHOOSE step \in ProfileFormalCommitSteps(profile) : TRUE]
ProfileKernelEventClaimant(profile) ==
    [event \in ProfileKernelEvidenceEvents(profile) |-> "builder"]
ProfileKernelEventOwner(profile) ==
    [event \in ProfileKernelEvidenceEvents(profile) |->
        ExpectedProfileCommitOwner(profile)]
ProfileKernelEventCommit(profile) ==
    ProfileKernelEventAction(profile)
ProfileKernelEventAssurance(profile) ==
    [event \in ProfileKernelEvidenceEvents(profile) |-> "at-commit"]
ProfileKernelEventEvidenceClass(profile) ==
    [event \in ProfileKernelEvidenceEvents(profile) |-> "evidence"]

ProfileKernelImplementationConformance(profile) ==
    /\ ProfileImplementationStates # {}
    /\ ProfileFormalStates # {}
    /\ CheckableImplementationConformance(
           ProfileImplementationStates, ProfileFormalStates,
           ProfileImplementationInitial, ProfileFormalInitial,
           ProfileImplementationSteps(profile), ProfileFormalSteps(profile),
           ProfileImplementationCommitSteps(profile),
           ProfileFormalCommitSteps(profile),
           ProfileImplementationFailureSteps, ProfileFormalFailureSteps,
           ProfileImplementationProgressSteps(profile),
           ProfileFormalProgressSteps(profile),
           ProfileDeploymentSteps(profile),
           ProfileFormalEnvironmentSteps(profile),
           ProfileTrustedSteps(profile), ProfileObservationDomain,
           ProfileImplementationCommitOwner(profile),
           ProfileFormalCommitOwner(profile),
           ProfileImplementationCommitDelegate(profile),
           ProfileFormalCommitDelegate(profile),
           ProfileImplementationCommitAssurance(profile),
           ProfileFormalCommitAssurance(profile),
           ProfileImplementationPersistentObserve,
           ProfileFormalPersistentObserve,
           ProfileAbstraction, ProfileImplementationObserve,
           ProfileFormalObserve)

ProfileKernelSemanticCoherence(profile) ==
    /\ StateStepBoundaryCoherence(
           ProfileSelectedFamilies,
           ProfileFormalStates, ProfileFormalInitial,
           ProfileFormalSteps(profile), ProfileFormalSafeStates,
           ProfileFormalCommitSteps(profile), ProfileFormalFailureSteps,
           ProfileFormalEnvironmentSteps(profile),
           ProfileFormalCommitOwner(profile),
           ProfileFormalCommitDelegate(profile),
           ProfileFormalCommitAssurance(profile),
           ProfileFormalPersistentObserve,
           ProfileStates, ProfileFormalInitial, ProfileSafeStates,
           ProfileObligationSystemSteps(profile),
           ProfileObligationEnvironmentSteps(profile),
           ProfileKernelInterferenceSteps(profile),
           ProfileKernelGovernedCommitSteps(profile),
           ProfileStates, ProfileKernelActors(profile),
           ProfileKernelClaimant, ProfileKernelCommitOwner(profile),
           ProfileKernelCommitDelegate(profile), ProfileFormalFailureSteps,
           {}, ProfileFormalPersistentObserve,
           ProfileKernelAssurancePosition,
           ProfileStates, ProfileCompositionInitialStates,
           ProfileCompositionInvA, ProfileCompositionInvB,
           ProfileCompositionStepA(profile),
           ProfileCompositionStepB(profile),
           ProfileCompositionSharedSteps(profile),
           ProfileCompositionEnvironmentSteps(profile),
           ProfileCompositionFailureSteps, {})
    /\ ProgressRefinementCoherence(
           ProfileSelectedFamilies, ProfileSelectedClasses,
           ProfileImplementationStates, ProfileImplementationSteps(profile),
           ProfileImplementationProgressSteps(profile),
           ProfileImplementationOtherSteps(profile),
           ProfileImplementationClosedStates,
           ProfileFormalStates, ProfileFormalClosedStates,
           ProfileAbstraction)
    /\ RegistrationBoundaryCoherence(
           ProfileRegisteredGuarantees,
           ProfileBoundaryIds(profile), ProfileFailureCeilings(profile),
           ProfileGuaranteeBoundaryOf(profile),
           ProfileGuaranteeFailureCeilingOf(profile),
           ProfileFormalStates, ProfileFormalCommitSteps(profile),
           ProfileFormalFailureSteps, ProfileFormalObserve, {})
    /\ RefinementRegistrationCoherence(
           ProfileRegisteredGuarantees, ProfileGuaranteeFamily,
           ProfileGuaranteePropertyClass, ProfileSelectedClasses)
    /\ EvidenceRegistrationCoherence(
           ProfileRegisteredGuarantees, ProfileGuaranteePropertyClass,
           ProfileSupportedGuaranteeKinds(profile),
           ProfileKernelEvidenceEvents(profile), ProfileObservationDomain,
           ProfileKernelEvidenceSubjects, ProfileKernelActors(profile),
           ProfileFormalSteps(profile), ProfileFormalCommitSteps(profile),
           ProfileKernelEvidenceCommitActionLinks(profile),
           ProfileKernelEventObservation(profile),
           ProfileKernelEventSubject(profile),
           ProfileKernelEventAction(profile),
           ProfileKernelEventClaimant(profile),
           ProfileKernelEventOwner(profile),
           ProfileKernelEventCommit(profile),
           ProfileKernelEventAssurance(profile),
           ProfileKernelEventEvidenceClass(profile),
           ProfileFormalCommitOwner(profile),
           ProfileFormalCommitAssurance(profile),
           ProfileFormalObserve, ProfileFormalPersistentObserve,
           ProfileKernelClaimant)

ProfileConstructionFullPremisesHeld(profile) ==
    ConstructionAdmitted(
        ProfileRetainedStructuresForKernel,
        ProfileSelectedStructuresForKernel(profile),
        RetainedExecutionModalityNames,
        ProfileSelectedExecutionCarrier(profile),
        ProfileInstances(profile), ProfileStructureOf(profile),
        ProfileParameterDomain, ProfileParameterDomainOf(profile),
        ProfileParameters(profile), ProfileSelectedFamilies,
        ProfileDeclaredGlobalAssumptions, ProfileLibraryPremises,
        ProfileDeploymentPremises, ProfileDischargedPremises,
        ProfileRegisteredGuarantees, ProfileBoundaryIds(profile),
        ProfileFailureCeilings(profile), ProfileGuaranteeFamily,
        ProfileGuaranteeKindOf, ProfileGuaranteePropertyClass,
        ProfileGuaranteeBoundaryOf(profile),
        ProfileGuaranteeFailureCeilingOf(profile),
        ProfileSupportedGuaranteeKinds(profile),
        ProfileKernelSemanticCoherence(profile),
        ProfileKernelImplementationConformance(profile),
        ProfileObligationFamilyPremises(profile),
        ProfileCheckActFamilyPremises(profile), FALSE,
        ProfileOwnershipAssuranceFamilyPremises(profile),
        ProfileCompositionFamilyPremises(profile),
        ProfileSafetyRefinementPremisesHeld(profile)
          /\ ProfileObservationRefinementPremisesHeld)
ProfileConstructionGuaranteeHeld(profile) ==
    RegisteredConstructionGuaranteeBundle(
        ProfileRetainedStructuresForKernel,
        ProfileSelectedStructuresForKernel(profile),
        ProfileInstances(profile), ProfileStructureOf(profile),
        ProfileParameterDomain, ProfileParameterDomainOf(profile),
        ProfileParameters(profile), ProfileSelectedFamilies,
        ProfileRegisteredGuarantees, ProfileBoundaryIds(profile),
        ProfileFailureCeilings(profile), ProfileGuaranteeFamily,
        ProfileGuaranteeKindOf, ProfileGuaranteePropertyClass,
        ProfileGuaranteeBoundaryOf(profile),
        ProfileGuaranteeFailureCeilingOf(profile),
        ProfileSupportedGuaranteeKinds(profile),
        ProfileObligationFamilyConclusion(profile),
        ProfileCheckActFamilyConclusion(profile), FALSE,
        ProfileOwnershipAssuranceFamilyConclusion(profile),
        ProfileCompositionFamilyConclusion(profile),
        ProfileSafetyRefinementConclusionHeld(profile)
          /\ ProfileObservationRefinementConclusionHeld)

ProfileSelectedObligationBoundaryHeld(profile) ==
    /\ ExactRetainedObligationRegistryBinding(
           Structures, ExecutionModalities,
           ObligationOccurrences, Obligations,
           StructureObligationOccurrences,
           ExecutionModalityObligationOccurrences,
           NormalizedKeyOf, ObligationPropertyClass,
           RegistryStructureNames, RegistryExecutionModalityNames,
           RegistryObligationOccurrenceNames,
           RegistryNormalizedObligationNames,
           RegistryCarrierObligationOccurrences,
           RegistryNormalizedKeyOf,
           RegistryObligationPropertyClassOf)
    /\ ALKConstructionSelectionTyped(
           ProfileClaims(profile), Structures, ExecutionModalities,
           ObligationOccurrences, Obligations,
           StructureObligationOccurrences,
           ExecutionModalityObligationOccurrences,
           NormalizedKeyOf, ProfileSelectedStructuresForClaim(profile),
           [claim \in ProfileClaims(profile) |->
               ProfileSelectedExecutionModality(profile)],
           ProfileCompositionSeamObligationOccurrences(profile),
           ProfileClaimObligationOccurrences(profile),
           ProfileClaimObligations(profile))
    /\ SelectedObligationBoundaryTyped(
           ProfileStates, ProfileActionLabels, ProfilePotentialActions,
           ProfileClaims(profile), Obligations, ProfileActors,
           ObligationPropertyClass, ProfileClaimObligations(profile),
           ProfileObligationStates, ProfileViolationStates,
           ProfileAllowedRelationSteps, ProfileViolatingActions,
           ProfileDerivedFrom, ProfileLivenessActiveStates,
           ProfileLivenessClosedStates, ProfileLivenessProgressActions,
           ProfileLivenessOtherActions,
           ProfileLivenessWeakFairProgressActions,
           ProfileLivenessRankBound, ProfileLivenessRank,
           ProfileLivenessFairnessOwner(profile),
           ProfileLivenessFairnessOwnerOf(profile))

ProfileMediationPremisesHeld(profile) ==
    GovernedCommitMediationPremises(
        ProfileStates, ProfileClaims(profile), Obligations,
        ProfileActionLabels, ProfilePotentialActions, ProfileActors,
        ProfileClaimActions(profile), ProfileAdmittedActions(profile),
        ProfileClaimObligations(profile), ObligationPropertyClass,
        ProfileViolatingActions, ProfileLivenessProgressActions,
        ProfileObligationRelevantActions(profile),
        ProfilePathClassOf(profile),
        ProfileGovernedCommitSteps(profile),
        ProfileClaimCommitActions(profile),
        ProfileGovernedActions(profile), ProfileOwnerOf(profile),
        ProfileALKAuthority(profile))
ProfileMediationConclusionHeld(profile) ==
    GovernedCommitMediationConclusion(
        ProfileClaims(profile), ProfileClaimActions(profile),
        ProfileObligationRelevantActions(profile),
        ProfileGovernedActions(profile), ProfilePathClassOf(profile))
ProfileMediationEnforcementHeld(profile) ==
    MediationEnforcementPremises(
        ProfileStates, ProfileClaims(profile), Obligations,
        ProfileActionLabels, ProfileAdmittedActions(profile),
        ProfileGovernedActions(profile),
        ProfileClaimObligations(profile), ProfileObligationStates,
        ProfilePostMediationSteps(profile),
        ProfileFormalStepsForClaim(profile))
ProfileLivenessKernelBindingHeld(profile) ==
    ExactLivenessKernelBinding(
        ProfileClaims(profile), Obligations, ProfileActionLabels,
        ProfilePotentialActions, ProfileActors,
        ProfileClaimObligations(profile), ObligationPropertyClass,
        ProfileLivenessClosedStates, ProfileLivenessProgressActions,
        ProfileLivenessOtherActions, ProfileLivenessRankBound,
        ProfileLivenessRank, ProfileLivenessFairnessOwner(profile),
        ProfileLivenessFairnessOwnerOf(profile), ProfileSelectedFamilies,
        ProfileFormalClosedStates, ProfileFormalProgressSteps(profile),
        ProfileFormalOtherSteps(profile), ProfileRankBound,
        ProfileFormalRank, ProfileFairnessOwner(profile),
        ProfileFormalFairnessOwnerOf(profile))
ProfileCommitAssuranceInventoryHeld(profile) ==
    CommitAssuranceInventoryTyped(
        ProfileClaims(profile), ProfileActionLabels, ProfileActors,
        ProfileProviders, ProfileClaimCommitActions(profile),
        ProfileGuaranteeClaimant(profile), ProfileOwnerOf(profile),
        ProfileAssuranceProviderOf, ProfileAssurancePositionOf,
        ProfilePreventionControllers, ProfileUnavailableProviders,
        ProfilePersistentEvidenceFor, ProfileRecoveryAvailableFor)
ProfileDerivedNormalGuaranteeBundle(profile) ==
    ResultingClaimGuaranteeBundle(
        profile, ProfileRegisteredGuarantees, ProfileGuaranteeKindOf,
        ProfileClaimCommitActions(profile),
        ProfileGuaranteeClaimant(profile), ProfileOwnerOf(profile),
        ProfileAssuranceProviderOf, ProfileAssurancePositionOf,
        ProfilePreventionControllers, ProfileUnavailableProviders,
        ProfilePersistentEvidenceFor, ProfileRecoveryAvailableFor)
ProfileAdvertisedGuaranteeBundle(profile) ==
    [claim \in ProfileClaims(profile) |->
        ProfileDerivedNormalGuaranteeBundle(profile)]
ProfileGuaranteeBundleHeld(profile) ==
    ClaimGuaranteeBundleMatchesDerived(
        ProfileClaims(profile),
        ProfileAdvertisedGuaranteeBundle(profile),
        ProfileRegisteredGuarantees, ProfileGuaranteeKindOf,
        ProfileClaimCommitActions(profile),
        ProfileGuaranteeClaimant(profile), ProfileOwnerOf(profile),
        ProfileAssuranceProviderOf, ProfileAssurancePositionOf,
        ProfilePreventionControllers, ProfileUnavailableProviders,
        ProfilePersistentEvidenceFor, ProfileRecoveryAvailableFor)

ProfileCommitEvidencePremisesHeld(profile) ==
    OwnedCommitEvidencePremises(
        ProfileStates, ProfileKernelCheckActMode,
        ProfileKernelCheckResultStates, ProfileKernelPredicateStates,
        ProfileKernelInterferenceSteps(profile),
        ProfileGovernedCommitSteps(profile),
        ProfileClaims(profile), ProfileSubjects, ProfileActionLabels,
        ProfileActors, ProfileProviders, ProfileEvidenceEvents(profile),
        ProfileClaimCommitActions(profile),
        ProfileEvidenceRequiredActions(profile),
        ProfileEvidenceForCommit(profile), ProfileClaimSubject(profile),
        ProfileGuaranteeClaimant(profile), ProfileOwnerOf(profile),
        ProfileAssurancePositionOf, ProfileEventSubject(profile),
        ProfileEventAction(profile), ProfileEventClaimant(profile),
        ProfileEventOwner(profile), ProfileEventCommit(profile),
        ProfileEventAssurance(profile), ProfileEvidenceProducer(profile),
        ProfileCustodianOf(profile), ProfileRetentionProviderOf(profile))
ProfileEvidenceRequirementBindingHeld(profile) ==
    ExactEvidenceRequirementBinding(
        ProfileClaims(profile), ProfileActionLabels,
        ProfileRegisteredGuarantees, ProfileGuaranteeKindOf,
        ProfileGuaranteePropertyClass,
        ProfileClaimCommitActions(profile),
        ProfileEvidenceRequiredActions(profile))
ProfileCommitEvidenceConclusionHeld(profile) ==
    OwnedCommitEvidenceConclusion(
        ProfileStates, ProfileKernelPredicateStates,
        ProfileGovernedCommitSteps(profile), ProfileClaims(profile),
        ProfileEvidenceRequiredActions(profile),
        ProfileEvidenceForCommit(profile), ProfileEventAssurance(profile))

ProfileProviderBackedRelyPremisesHeld(profile) ==
    ProviderBackedRelyPremises(
        ProfileStates, ProfileComponents, ProfileRelyEdges(profile),
        ProfileRelyRank(profile), ProfileRelyPropertyClassOf(profile),
        ProfileDirectMutualClosureEdges(profile),
        ProfileComponentObligationStates,
        ProfileComponentRelySteps(profile),
        ProfileComponentGuaranteeSteps(profile),
        ProfileSharedStepsForRelyEdge(profile),
        ProfileRegisteredSharedSteps(profile))
ProfileProviderBackedRelyConclusionHeld(profile) ==
    ProviderBackedRelyConclusion(
        ProfileComponents, ProfileRelyEdges(profile),
        ProfileRelyRank(profile), ProfileRelyPropertyClassOf(profile),
        ProfileDirectMutualClosureEdges(profile),
        ProfileComponentRelySteps(profile),
        ProfileComponentGuaranteeSteps(profile))
ProfileSharedTransitionPremisesHeld(profile) ==
    SharedTransitionPremises(
        ProfileStates, ProfileComponents,
        ProfileRepresentedSharedSteps(profile),
        ProfileRegisteredSharedSteps(profile),
        ProfileAffectedComponents, ProfileComponentObligationStates)
ProfileSharedTransitionConclusionHeld(profile) ==
    SharedTransitionPreservation(
        ProfileStates, ProfileRegisteredSharedSteps(profile),
        ProfileAffectedComponents, ProfileComponentObligationStates)

ProfileFailureInputsHeld ==
    FailureInputsTyped(TRUE, TRUE, TRUE, TRUE, TRUE, TRUE, TRUE, TRUE)
ProfileBypassFailureInputBindingHeld(profile) ==
    ExactBypassFailureInputBinding(
        ProfileClaims(profile), ProfileActionLabels,
        ProfilePotentialActions, ProfileClaimActions(profile),
        ProfilePathClassOf(profile), TRUE)
ProfileDerivedFailureBundle(profile) ==
    DerivedFailureGuaranteeBundle(
        ProfileDerivedNormalGuaranteeBundle(profile),
        TRUE, TRUE, TRUE, TRUE, TRUE, TRUE, TRUE, TRUE)
ProfileFailureBundleHeld(profile) ==
    /\ NamedFailureNarrowingConclusion(
           ProfileDerivedNormalGuaranteeBundle(profile),
           TRUE, TRUE, TRUE, TRUE, TRUE, TRUE, TRUE, TRUE)
    /\ FailureGuaranteeBundleMatchesDerived(
           ProfileDerivedFailureBundle(profile),
           ProfileDerivedNormalGuaranteeBundle(profile),
           TRUE, TRUE, TRUE, TRUE, TRUE, TRUE, TRUE, TRUE)
ProfileFailureLedger(profile) ==
    [failureClass \in ALKFailureClasses |->
        ProfileFailureScenarioCeiling(
            failureClass, ProfileDerivedNormalGuaranteeBundle(profile))]
ProfileExactFailureLedgerHeld(profile) ==
    ExactProfileFailureLedger(
        ProfileDerivedNormalGuaranteeBundle(profile),
        ProfileFailureLedger(profile))

ProfileTCBClosureHeld(profile) ==
    ExactClaimTCBClosure(
        ProfileClaims(profile), Obligations, ProfileActionLabels,
        ProfileActors, ProfileProviders, ProfileEvidenceEvents(profile),
        Dependencies, ProfileClaimTCB(profile),
        ProfileClaimObligations(profile), ObligationPropertyClass,
        ProfileLivenessFairnessOwner(profile),
        ProfileGuaranteeClaimant(profile), ProfileALKAuthority(profile),
        ProfileAdmittedActions(profile),
        ProfileClaimCommitActions(profile), ProfileOwnerOf(profile),
        ProfileDelegateOf, ProfileAssuranceProviderOf,
        ProfileActorDependency, ProfileEvidenceForCommit(profile),
        ProfileEvidenceProducer(profile), ProfileCustodianOf(profile),
        ProfileRetentionProviderOf(profile), ProfileProviderDependency)
ProfileRequiredDependenciesBefore(profile) ==
    MechanicallyRequiredClaimDependencies(
        ProfileClaims(profile), ProfileClaimObligations(profile),
        ObligationPropertyClass, ProfileLivenessFairnessOwner(profile),
        ProfileGuaranteeClaimant(profile), ProfileALKAuthority(profile),
        ProfileAdmittedActions(profile),
        ProfileClaimCommitActions(profile), ProfileOwnerOf(profile),
        ProfileDelegateOf, ProfileAssuranceProviderOf,
        ProfileActorDependency, ProfileEvidenceForCommit(profile),
        ProfileEvidenceProducer(profile), ProfileCustodianOf(profile),
        ProfileRetentionProviderOf(profile), ProfileProviderDependency)
ProfileTCBRequirementGrowthBindingHeld(profile) ==
    ExactTCBRequirementGrowthBinding(
        ProfileClaims(profile), Dependencies,
        ProfileClaimObligations(profile), ObligationPropertyClass,
        ProfileLivenessFairnessOwner(profile),
        ProfileGuaranteeClaimant(profile), ProfileALKAuthority(profile),
        ProfileAdmittedActions(profile),
        ProfileClaimCommitActions(profile), ProfileOwnerOf(profile),
        ProfileDelegateOf, ProfileAssuranceProviderOf,
        ProfileActorDependency, ProfileEvidenceForCommit(profile),
        ProfileEvidenceProducer(profile), ProfileCustodianOf(profile),
        ProfileRetentionProviderOf(profile), ProfileProviderDependency,
        ProfileRequiredDependenciesBefore(profile), {"future-adapter"})
ProfileTCBMonotonicityHeld(profile) ==
    FixedClaimTCBMonotonicity(
        Dependencies, ProfileRequiredDependenciesBefore(profile),
        {"future-adapter"})

ProfileKernelSelectionBindingHeld(profile) ==
    KernelSelectionGuaranteeBinding(
           ProfileClaims(profile), Structures, ExecutionModalities,
           Obligations, ProfileStates,
           ProfileSelectedStructuresForClaim(profile),
           [claim \in ProfileClaims(profile) |->
               ProfileSelectedExecutionModality(profile)],
           ProfileClaimObligations(profile), ObligationPropertyClass,
           ProfileObligationStates,
           ProfileSelectedStructuresForKernel(profile),
           ProfileSelectedExecutionCarrier(profile),
           ProfileRegisteredGuarantees, ProfileGuaranteeFamily,
           ProfileGuaranteePropertyClass,
           ProfileGuaranteeObligations(profile), ProfileSafeStates)
ProfileKernelCommitAssuranceBindingHeld(profile) ==
    KernelCommitAssuranceBinding(
           ProfileClaims(profile), ProfileActionLabels,
           ProfilePotentialActions, ProfilePostMediationSteps(profile),
           ProfileClaimCommitActions(profile),
           ProfileGuaranteeClaimant(profile), ProfileOwnerOf(profile),
           ProfileDelegateOf, ProfileAssuranceProviderOf,
           ProfileAssurancePositionOf, ProfilePreventionControllers,
           ProfileUnavailableProviders, ProfilePersistentEvidenceFor,
           ProfileRecoveryAvailableFor, ProfileFormalCommitSteps(profile),
           ProfileFormalCommitOwner(profile),
           ProfileFormalCommitDelegate(profile),
           ProfileFormalCommitAssurance(profile), ProfileKernelClaimant,
           ProfileKernelAssuranceProvider,
           ProfileKernelPreventionControllers,
           ProfileKernelUnavailableProviders,
           ProfileKernelPersistentEvidence,
           ProfileKernelRecoveryAvailable)
ProfileKernelCompositionBindingHeld(profile) ==
    KernelCompositionBinding(
           ProfileComponents, ProfileRelyEdges(profile),
           ProfileComponentObligationStates,
           ProfileComponentRelySteps(profile),
           ProfileComponentGuaranteeSteps(profile),
           ProfileRegisteredSharedSteps(profile),
           ProfileRelyEdges(profile), ProfileCompositionInvA,
           ProfileCompositionInvB, ProfileCompositionRelyA(profile),
           ProfileCompositionRelyB(profile),
           ProfileCompositionStepA(profile),
           ProfileCompositionStepB(profile),
           ProfileCompositionSharedSteps(profile))
ProfileKernelEvidenceBindingHeld(profile) ==
    KernelEvidenceBinding(
           ProfileClaims(profile), ProfileEvidenceEvents(profile),
           ProfileKernelEvidenceEvents(profile),
           ProfileEvidenceRequiredActions(profile),
           ProfileEvidenceForCommit(profile),
           ProfileFormalCommitSteps(profile),
           ProfileEvidenceKernelEvent(profile),
           ProfileEventObservation(profile), ProfileEventSubject(profile),
           ProfileEventAction(profile), ProfileEventClaimant(profile),
           ProfileEventOwner(profile), ProfileEventCommit(profile),
           ProfileEventAssurance(profile),
           ProfileEventEvidenceClass(profile),
           ProfilePostMediationSteps(profile),
           ProfileKernelEventObservation(profile),
           ProfileKernelEventSubject(profile),
           ProfileKernelEventAction(profile),
           ProfileKernelEventClaimant(profile),
           ProfileKernelEventOwner(profile),
           ProfileKernelEventCommit(profile),
           ProfileKernelEventAssurance(profile),
           ProfileKernelEventEvidenceClass(profile))
ProfileKernelBoundaryReuseHeld(profile) ==
    /\ "check-act" \in ProfileSelectedFamilies
    /\ "composition" \in ProfileSelectedFamilies
    /\ ProfileKernelGovernedCommitSteps(profile) =
         ProfileFormalCommitSteps(profile)
    /\ \A claim \in ProfileClaims(profile) :
          ProfileFormalStepsForClaim(profile)[claim] =
            ProfileFormalSteps(profile)
    /\ ProfileKernelSelectionBindingHeld(profile)
    /\ ProfileKernelCommitAssuranceBindingHeld(profile)
    /\ ProfileKernelCompositionBindingHeld(profile)
    /\ ProfileKernelEvidenceBindingHeld(profile)

ProfileCommitSourceStates(profile) ==
    {pair[1] : pair \in ProfileGovernedCommitSteps(profile)}
ProfileAuthorizedCommitSourceStates(profile) ==
    CASE profile = "bounded-distributed" -> {"reconfigured"}
      [] OTHER -> {"open"}
ProfileAvailableAuthorizationStates(profile) ==
    CASE profile = "bounded-distributed" -> {"reconfigured"}
      [] OTHER -> {"open"}
ProfileFailSafeAdmissionHeld(profile) ==
    /\ ProfileCommitSourceStates(profile) =
         ProfileAuthorizedCommitSourceStates(profile)
    /\ FailSafeAdmission(
           ProfileStates, ProfileGovernedCommitSteps(profile),
           ProfileAuthorizedCommitSourceStates(profile),
           ProfileAvailableAuthorizationStates(profile))
ProfileLocalBoundaryHeld(profile) ==
    /\ ProfileSelectionBoundaryTyped(
           profile, Structures, ExecutionModalities,
           ProfileSelectedStructures(profile),
           ProfileSelectedExecutionModality(profile))
    /\ profile = "local-reference"
    /\ ExpectedProfileCommitOwner(profile) = "builder"
    /\ ProfileKernelClaimant = ProfileKernelCommitOwner(profile)
    /\ ProfileKernelPersistentEvidence
    /\ ProfileTopologyBoundaryHeld(profile)
    /\ ProfileFailSafeAdmissionHeld(profile)
ProfileModularBoundaryHeld(profile) ==
    /\ ProfileSelectionBoundaryTyped(
           profile, Structures, ExecutionModalities,
           ProfileSelectedStructures(profile),
           ProfileSelectedExecutionModality(profile))
    /\ profile = "modular"
    /\ ProfileRelyEdges(profile) = PossibleRelyEdges
    /\ ProfileDirectMutualClosureEdges(profile) = PossibleRelyEdges
    /\ ProfileRegisteredSharedSteps(profile) # {}
    /\ ProfileSharedTransitionPremisesHeld(profile)
    /\ ProfilePotentialActions["bypass"] = {}
    /\ ProfileTopologyBoundaryHeld(profile)
    /\ ProfileFailSafeAdmissionHeld(profile)
ProfileDelegatedBoundaryHeld(profile) ==
    /\ ProfileSelectionBoundaryTyped(
           profile, Structures, ExecutionModalities,
           ProfileSelectedStructures(profile),
           ProfileSelectedExecutionModality(profile))
    /\ profile = "delegated"
    /\ ExpectedProfileCommitOwner(profile) = "external-owner"
    /\ ProfileKernelClaimant # ProfileKernelCommitOwner(profile)
    /\ DelegatedVariantCeilingsExact
    /\ ProfileTopologyBoundaryHeld(profile)
    /\ ProfileFailSafeAdmissionHeld(profile)

ProfileEpochs == {"epoch-0", "epoch-1"}
ProfileMembershipOf ==
    [state \in ProfileStates |->
        IF state = "open"
          THEN {"node-a", "node-b"}
          ELSE {"node-b", "node-c"}]
ProfileEpochOf ==
    [state \in ProfileStates |->
        IF state = "open" THEN "epoch-0" ELSE "epoch-1"]
ProfileAllowedDecisionSets ==
    [state \in ProfileStates |->
        IF state = "open"
          THEN {{"node-a", "node-b"}}
          ELSE {{"node-b", "node-c"}}]
ProfileCollectiveCommitSteps == {<<"reconfigured", "closed">>}
ProfileCommitDecisionMembers ==
    [step \in ProfileCollectiveCommitSteps |-> {"node-b", "node-c"}]
ProfileCommitEpoch ==
    [step \in ProfileCollectiveCommitSteps |-> "epoch-1"]
ProfilePartitionedStates == {"failed"}
ProfileReconfigurationSteps == {<<"open", "reconfigured">>}
ProfileRetrySteps == {<<"reconfigured", "reconfigured">>}
ProfilePartitionSteps == {<<"reconfigured", "failed">>}
ProfileRecoverySteps == {<<"failed", "reconfigured">>}
ProfileDistributedBoundaryHeld(profile) ==
    /\ ProfileSelectionBoundaryTyped(
           profile, Structures, ExecutionModalities,
           ProfileSelectedStructures(profile),
           ProfileSelectedExecutionModality(profile))
    /\ profile = "bounded-distributed"
    /\ ExpectedProfileCommitOwner(profile) = "cluster-owner"
    /\ DistributedProfileBoundaryTyped(
           ProfileStates, {"node-a", "node-b", "node-c"},
           ProfileEpochs, ProfileMembershipOf, ProfileEpochOf,
           ProfileAllowedDecisionSets, ProfileCollectiveCommitSteps,
           ProfileCommitDecisionMembers, ProfileCommitEpoch,
           ProfilePartitionedStates, ProfileReconfigurationSteps,
           ProfileRetrySteps, ProfileRecoverySteps)
    /\ ProfileCollectiveCommitSteps =
         ProfileFormalCommitSteps(profile)
    /\ ProfileReconfigurationSteps =
         ProfilePostMediationSteps(profile)["reconfigure"]
    /\ ProfileRetrySteps = ProfilePostMediationSteps(profile)["retry"]
    /\ ProfileRecoverySteps =
         ProfilePostMediationSteps(profile)["recover"]
    /\ DistributedExecutionBoundaryTyped(
           ProfileStates, ProfileMembershipOf, ProfileEpochOf,
           ProfilePartitionedStates, ProfileReconfigurationSteps,
           ProfileRetrySteps, ProfilePartitionSteps,
           ProfileRecoverySteps, ProfileCollectiveCommitSteps)
    /\ ProfileTopologyBoundaryHeld(profile)
    /\ ProfileFailSafeAdmissionHeld(profile)

ProfileSpecificBoundaryHeld(profile) ==
    CASE profile = "local-reference" -> ProfileLocalBoundaryHeld(profile)
      [] profile = "modular" -> ProfileModularBoundaryHeld(profile)
      [] profile = "delegated" -> ProfileDelegatedBoundaryHeld(profile)
      [] profile = "bounded-distributed" ->
           ProfileDistributedBoundaryHeld(profile)

ProfileAcceptedTheoremPremisesHeld(profile) ==
    /\ ProfileSelectedObligationBoundaryHeld(profile)
    /\ ProfileConstructionFullPremisesHeld(profile)
    /\ ProfileMediationPremisesHeld(profile)
    /\ ProfileMediationEnforcementHeld(profile)
    /\ ProfileLivenessKernelBindingHeld(profile)
    /\ ProfileCommitAssuranceInventoryHeld(profile)
    /\ ProfileEvidenceRequirementBindingHeld(profile)
    /\ ProfileCommitEvidencePremisesHeld(profile)
    /\ ProfileProviderBackedRelyPremisesHeld(profile)
    /\ ProfileSharedTransitionPremisesHeld(profile)
    /\ ProfileFailureInputsHeld
    /\ ProfileBypassFailureInputBindingHeld(profile)
    /\ ProfileTCBClosureHeld(profile)
    /\ ProfileTCBRequirementGrowthBindingHeld(profile)
    /\ ProfileKernelBoundaryReuseHeld(profile)

ProfileTheoremEntryPremisesHeld(profile) ==
    /\ ProfileAcceptedTheoremPremisesHeld(profile)
    /\ ProfileSpecificBoundaryHeld(profile)

ProfileAcceptedTheoremConclusionsHeld(profile) ==
    /\ ProfileConstructionGuaranteeHeld(profile)
    /\ ProfileMediationConclusionHeld(profile)
    /\ ProfileGuaranteeBundleHeld(profile)
    /\ ProfileCommitEvidenceConclusionHeld(profile)
    /\ ProfileProviderBackedRelyConclusionHeld(profile)
    /\ ProfileSharedTransitionConclusionHeld(profile)
    /\ ProfileFailureBundleHeld(profile)
    /\ ProfileTCBMonotonicityHeld(profile)

ProfileTheoremEntryConclusionsHeld(profile) ==
    /\ ProfileAcceptedTheoremConclusionsHeld(profile)
    /\ ProfileExactFailureLedgerHeld(profile)

AllProfilePremisesHeld ==
    \A profile \in ProfileNames : ProfileTheoremEntryPremisesHeld(profile)
AllProfileConclusionsHeld ==
    \A profile \in ProfileNames : ProfileTheoremEntryConclusionsHeld(profile)
AllProfilesProductionSurfacesHeld ==
    \A profile \in ProfileNames :
        /\ ProfileTheoremEntryPremisesHeld(profile)
        /\ ProfileTheoremEntryConclusionsHeld(profile)

LocalReferenceProfilePremisesHeld ==
    ProfileTheoremEntryPremisesHeld("local-reference")
LocalReferenceSelectionHeld ==
    ProfileSelectedObligationBoundaryHeld("local-reference")
LocalReferenceConstructionHeld ==
    ProfileConstructionFullPremisesHeld("local-reference")
LocalReferenceMediationHeld ==
    ProfileMediationPremisesHeld("local-reference")
LocalReferenceEnforcementHeld ==
    ProfileMediationEnforcementHeld("local-reference")
LocalReferenceLivenessBindingHeld ==
    ProfileLivenessKernelBindingHeld("local-reference")
LocalReferenceCommitAssuranceHeld ==
    ProfileCommitAssuranceInventoryHeld("local-reference")
LocalReferenceEvidenceRequirementHeld ==
    ProfileEvidenceRequirementBindingHeld("local-reference")
LocalReferenceCommitEvidenceHeld ==
    ProfileCommitEvidencePremisesHeld("local-reference")
LocalReferenceRelyHeld ==
    ProfileProviderBackedRelyPremisesHeld("local-reference")
LocalReferenceSharedHeld ==
    ProfileSharedTransitionPremisesHeld("local-reference")
LocalReferenceFailureInputsHeld == ProfileFailureInputsHeld
LocalReferenceBypassBindingHeld ==
    ProfileBypassFailureInputBindingHeld("local-reference")
LocalReferenceTCBHeld == ProfileTCBClosureHeld("local-reference")
LocalReferenceTCBGrowthHeld ==
    ProfileTCBRequirementGrowthBindingHeld("local-reference")
LocalReferenceKernelReuseHeld ==
    ProfileKernelBoundaryReuseHeld("local-reference")
LocalReferenceKernelSelectionHeld ==
    ProfileKernelSelectionBindingHeld("local-reference")
LocalReferenceKernelCommitAssuranceHeld ==
    ProfileKernelCommitAssuranceBindingHeld("local-reference")
LocalReferenceKernelCompositionHeld ==
    ProfileKernelCompositionBindingHeld("local-reference")
LocalReferenceKernelEvidenceHeld ==
    ProfileKernelEvidenceBindingHeld("local-reference")
LocalReferenceSpecificBoundaryHeld ==
    ProfileSpecificBoundaryHeld("local-reference")
ModularSpecificBoundaryHeld ==
    ProfileSpecificBoundaryHeld("modular")
DelegatedSpecificBoundaryHeld ==
    ProfileSpecificBoundaryHeld("delegated")
BoundedDistributedSpecificBoundaryHeld ==
    ProfileSpecificBoundaryHeld("bounded-distributed")
ModularProfilePremisesHeld ==
    ProfileTheoremEntryPremisesHeld("modular")
DelegatedProfilePremisesHeld ==
    ProfileTheoremEntryPremisesHeld("delegated")
BoundedDistributedProfilePremisesHeld ==
    ProfileTheoremEntryPremisesHeld("bounded-distributed")

LocalReferenceProfileConclusionsHeld ==
    ProfileTheoremEntryConclusionsHeld("local-reference")
ModularProfileConclusionsHeld ==
    ProfileTheoremEntryConclusionsHeld("modular")
DelegatedProfileConclusionsHeld ==
    ProfileTheoremEntryConclusionsHeld("delegated")
BoundedDistributedProfileConclusionsHeld ==
    ProfileTheoremEntryConclusionsHeld("bounded-distributed")

====
