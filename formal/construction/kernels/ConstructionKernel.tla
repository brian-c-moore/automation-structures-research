---- MODULE ConstructionKernel ----
EXTENDS RefinementKernel, OwnershipAssuranceKernel, CompositionKernel

KernelFamilies ==
    {"obligation", "check-act", "progress", "ownership-assurance",
     "composition", "refinement"}

RequiredConstructionFamilies ==
    {"obligation", "ownership-assurance", "refinement"}

KernelTracePropertyClasses == {"safety", "liveness", "evidence"}

FamilyPropertyClasses ==
    [family \in KernelFamilies |->
        CASE family = "obligation" -> {"safety"}
          [] family = "check-act" -> {"safety"}
          [] family = "progress" -> {"liveness"}
          [] family = "ownership-assurance" -> {"safety"}
          [] family = "composition" -> {"safety"}
          [] OTHER -> {"safety", "liveness", "evidence"}]

KernelFamilyPremiseName ==
    [family \in KernelFamilies |->
        CASE family = "obligation" -> "obligation-preservation"
          [] family = "check-act" -> "check-act-stability"
          [] family = "progress" -> "ranked-progress"
          [] family = "ownership-assurance" -> "ownership-assurance-ceiling"
          [] family = "composition" -> "composition-safety"
          [] OTHER -> "class-specific-refinement-transfer"]

SelectedFamilyPremiseNames(SelectedFamilies) ==
    {KernelFamilyPremiseName[family] : family \in SelectedFamilies}

ApplicableKernelClaims(
        SelectedFamilies,
        ObligationClaim, CheckActClaim, ProgressClaim,
        OwnershipAssuranceClaim, CompositionClaim, RefinementClaim) ==
    /\ ("obligation" \in SelectedFamilies => ObligationClaim)
    /\ ("check-act" \in SelectedFamilies => CheckActClaim)
    /\ ("progress" \in SelectedFamilies => ProgressClaim)
    /\ ("ownership-assurance" \in SelectedFamilies
          => OwnershipAssuranceClaim)
    /\ ("composition" \in SelectedFamilies => CompositionClaim)
    /\ ("refinement" \in SelectedFamilies => RefinementClaim)

GuaranteeBundleTyped(
        RegisteredGuarantees, SelectedFamilies,
        BoundaryIds, FailureCeilings,
        GuaranteeFamily, GuaranteeKindOf, GuaranteePropertyClass,
        GuaranteeBoundaryOf, GuaranteeFailureCeilingOf) ==
    /\ RegisteredGuarantees # {}
    /\ BoundaryIds # {}
    /\ FailureCeilings # {}
    /\ GuaranteeFamily \in [RegisteredGuarantees -> SelectedFamilies]
    /\ GuaranteeKindOf \in [RegisteredGuarantees -> GuaranteeKinds]
    /\ GuaranteePropertyClass
         \in [RegisteredGuarantees -> KernelTracePropertyClasses]
    /\ GuaranteeBoundaryOf \in [RegisteredGuarantees -> BoundaryIds]
    /\ GuaranteeFailureCeilingOf
         \in [RegisteredGuarantees -> FailureCeilings]

GuaranteeRegistrationCompatible(
        RegisteredGuarantees, SelectedFamilies,
        GuaranteeFamily, GuaranteeKindOf, GuaranteePropertyClass,
        SupportedGuaranteeKinds) ==
    /\ SupportedGuaranteeKinds \subseteq GuaranteeKinds
    /\ SelectedFamilies =
         {GuaranteeFamily[guarantee]
             : guarantee \in RegisteredGuarantees}
    /\ \A guarantee \in RegisteredGuarantees :
          /\ GuaranteePropertyClass[guarantee]
               \in FamilyPropertyClasses[GuaranteeFamily[guarantee]]
          /\ GuaranteeKindOf[guarantee] \in SupportedGuaranteeKinds

RefinementClassPropertyClass ==
    [class \in RefinementClasses |->
        IF class = "observation" THEN "evidence" ELSE class]

RefinementRegistrationCoherence(
        RegisteredGuarantees, GuaranteeFamily,
        GuaranteePropertyClass, SelectedClasses) ==
    /\ SelectedClasses # {}
    /\ SelectedClasses \subseteq RefinementClasses
    /\ {GuaranteePropertyClass[guarantee] :
            guarantee \in
              {candidate \in RegisteredGuarantees :
                  GuaranteeFamily[candidate] = "refinement"}}
         = {RefinementClassPropertyClass[class] :
                class \in SelectedClasses}

ConstructionBoundaryId(FormalStates, FormalCommitSteps, FormalObserve) ==
    <<FormalStates, FormalCommitSteps, FormalObserve>>

ConstructionFailureCeilingId(
        FormalFailureSteps, UnavailableProviders) ==
    <<FormalFailureSteps, UnavailableProviders>>

StateStepBoundaryCoherence(
        SelectedFamilies,
        FormalStates, FormalInitial, FormalSteps, FormalSafeStates,
        FormalCommitSteps, FormalFailureSteps, FormalEnvironmentSteps,
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
        CompositionStepA, CompositionStepB, CompositionSharedSteps,
        CompositionEnvironmentSteps, CompositionFailureSteps,
        CompositionUnavailableProviders) ==
    /\ ObligationStateDomain = FormalStates
    /\ ObligationInitialStates = FormalInitial
    /\ RegisteredObligationStates = FormalSafeStates
    /\ ObligationSystemSteps \cup ObligationEnvironmentSteps = FormalSteps
    /\ ObligationEnvironmentSteps = FormalEnvironmentSteps
    /\ FormalFailureSteps \subseteq FormalEnvironmentSteps
    /\ ObligationTyped(
           FormalStates, RegisteredObligationStates,
           FormalStates \ RegisteredObligationStates,
           AssuranceActors, AssuranceClaimant)
    /\ AssuranceStateDomain = FormalStates
    /\ AssuranceFailureSteps = FormalFailureSteps
    /\ AssurancePersistentEvidenceObserve = FormalPersistentObserve
    /\ DOMAIN FormalCommitOwner = FormalCommitSteps
    /\ DOMAIN FormalCommitDelegate = FormalCommitSteps
    /\ DOMAIN FormalCommitAssurance = FormalCommitSteps
    /\ \A step \in FormalCommitSteps :
          /\ FormalCommitOwner[step] = AssuranceCommitOwner
          /\ FormalCommitDelegate[step] = AssuranceCommitDelegate
          /\ FormalCommitAssurance[step] = KernelAssurancePosition
    /\ ("check-act" \in SelectedFamilies
          => /\ KernelGovernedCommitSteps = FormalCommitSteps
             /\ KernelInterferenceSteps =
                  FormalSteps \ FormalCommitSteps)
    /\ ("composition" \in SelectedFamilies
          => /\ CompositionStateDomain = FormalStates
             /\ CompositionInitialStates = FormalInitial
             /\ JointInvariant(CompositionInvA, CompositionInvB)
                  = FormalSafeStates
             /\ ComposedSteps(
                    CompositionStepA, CompositionStepB,
                    CompositionSharedSteps,
                    CompositionEnvironmentSteps,
                    CompositionFailureSteps) = FormalSteps
             /\ CompositionEnvironmentSteps
                  \cup CompositionFailureSteps = FormalEnvironmentSteps
             /\ CompositionFailureSteps = FormalFailureSteps
             /\ CompositionUnavailableProviders =
                  AssuranceUnavailableProviders)

ProgressRefinementCoherence(
        SelectedFamilies, SelectedClasses,
        ImplementationStates, ImplementationSteps,
        ImplementationProgressSteps, ImplementationOtherSteps,
        ImplementationClosedStates,
        FormalStates, FormalClosedStates, Abstraction) ==
    /\ DOMAIN Abstraction = ImplementationStates
    /\ "safety" \in SelectedClasses
    /\ ("progress" \in SelectedFamilies
          => /\ "liveness" \in SelectedClasses
             /\ ImplementationSteps =
                  ImplementationProgressSteps \cup ImplementationOtherSteps
             /\ ImplementationClosedStates =
                  ConcreteClosedStates(
                      ImplementationStates, FormalClosedStates,
                      Abstraction))

RegistrationBoundaryCoherence(
        RegisteredGuarantees, BoundaryIds, FailureCeilings,
        GuaranteeBoundaryOf, GuaranteeFailureCeilingOf,
        FormalStates, FormalCommitSteps, FormalFailureSteps,
        FormalObserve, UnavailableProviders) ==
    LET Boundary ==
          ConstructionBoundaryId(
              FormalStates, FormalCommitSteps, FormalObserve)
        FailureCeiling ==
          ConstructionFailureCeilingId(
              FormalFailureSteps, UnavailableProviders)
    IN
    /\ BoundaryIds = {Boundary}
    /\ FailureCeilings = {FailureCeiling}
    /\ \A guarantee \in RegisteredGuarantees :
          /\ GuaranteeBoundaryOf[guarantee] = Boundary
          /\ GuaranteeFailureCeilingOf[guarantee] = FailureCeiling

EvidenceRegistrationCoherence(
        RegisteredGuarantees, GuaranteePropertyClass,
        SupportedGuaranteeKinds,
        EvidenceEvents, ObservationDomain, EvidenceSubjects,
        EvidenceActors, FormalSteps, FormalCommitSteps,
        EvidenceCommitActionLinks,
        EventObservation, EventSubject, EventAction,
        EventClaimant, EventOwner, EventCommit,
        EventAssurance, EventEvidenceClass,
        FormalCommitOwner, FormalCommitAssurance,
        FormalObserve, FormalPersistentObserve,
        AssuranceClaimant) ==
    LET EvidenceGuarantees ==
          {guarantee \in RegisteredGuarantees :
              GuaranteePropertyClass[guarantee] = "evidence"}
        EvidenceRequired ==
          \/ EvidenceGuarantees # {}
          \/ "detection" \in SupportedGuaranteeKinds
          \/ "recovery" \in SupportedGuaranteeKinds
    IN
    IF EvidenceRequired
      THEN /\ EvidenceEvents # {}
           /\ EvidenceCommitActionLinks
                \subseteq FormalCommitSteps \X FormalSteps
           /\ EvidenceProfileTyped(
                  EvidenceEvents, ObservationDomain,
                  EvidenceSubjects, FormalSteps, EvidenceActors,
                  FormalCommitSteps, {"evidence"},
                  EventObservation, EventSubject, EventAction,
                  EventClaimant, EventOwner, EventCommit,
                  EventAssurance, EventEvidenceClass)
           /\ \A event \in EvidenceEvents :
                 /\ EventClaimant[event] = AssuranceClaimant
                 /\ <<EventCommit[event], EventAction[event]>>
                      \in EvidenceCommitActionLinks
                 /\ EventOwner[event] =
                      FormalCommitOwner[EventCommit[event]]
                 /\ EventAssurance[event] =
                      FormalCommitAssurance[EventCommit[event]]
                 /\ EventEvidenceClass[event] = "evidence"
                 /\ EventObservation[event] =
                      FormalObserve[EventAction[event][2]]
                 /\ FormalPersistentObserve[EventAction[event][2]]
      ELSE EvidenceEvents = {}

ConstructionStaticAdmission(
        RetainedStructures, SelectedStructures,
        RetainedExecutionCarriers, SelectedExecutionCarrier,
        Instances, StructureOf, ParameterDomain,
        ParameterDomainOf, Parameters,
        SelectedFamilies, DeclaredGlobalAssumptions,
        LibraryPremises, DeploymentPremises, DischargedPremises,
        RegisteredGuarantees, BoundaryIds, FailureCeilings,
        GuaranteeFamily, GuaranteeKindOf, GuaranteePropertyClass,
        GuaranteeBoundaryOf, GuaranteeFailureCeilingOf,
        SupportedGuaranteeKinds, SemanticCoherence,
        ImplementationConformance) ==
    /\ SelectedStructures # {}
    /\ Instances # {}
    /\ SelectedFamilies # {}
    /\ BuilderSelection(RetainedStructures, SelectedStructures)
    /\ RetainedExecutionCarriers \subseteq RetainedStructures
    /\ SelectedExecutionCarrier \in RetainedExecutionCarriers
    /\ SelectedExecutionCarrier \in SelectedStructures
    /\ BuilderInstantiation(
           SelectedStructures, Instances,
           StructureOf, ParameterDomain, ParameterDomainOf, Parameters)
    /\ RequiredConstructionFamilies \subseteq SelectedFamilies
    /\ SelectedFamilies \subseteq KernelFamilies
    /\ DeclaredGlobalAssumptions = GlobalModelingAssumptionNames
    /\ PremiseBoundary(
           LibraryPremises, DeploymentPremises, DischargedPremises)
    /\ DeclaredGlobalAssumptions \subseteq LibraryPremises
    /\ SelectedFamilyPremiseNames(SelectedFamilies)
         \subseteq LibraryPremises
    /\ GuaranteeBundleTyped(
           RegisteredGuarantees, SelectedFamilies,
           BoundaryIds, FailureCeilings,
           GuaranteeFamily, GuaranteeKindOf, GuaranteePropertyClass,
           GuaranteeBoundaryOf, GuaranteeFailureCeilingOf)
    /\ GuaranteeRegistrationCompatible(
           RegisteredGuarantees, SelectedFamilies,
           GuaranteeFamily, GuaranteeKindOf, GuaranteePropertyClass,
           SupportedGuaranteeKinds)
    /\ SemanticCoherence
    /\ ImplementationConformance

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
        SupportedGuaranteeKinds, SemanticCoherence,
        ImplementationConformance,
        ObligationPremises, CheckActPremises, ProgressPremises,
        OwnershipAssurancePremises, CompositionPremises,
        RefinementPremises) ==
    /\ ConstructionStaticAdmission(
           RetainedStructures, SelectedStructures,
           RetainedExecutionCarriers, SelectedExecutionCarrier,
           Instances, StructureOf, ParameterDomain,
           ParameterDomainOf, Parameters,
           SelectedFamilies, DeclaredGlobalAssumptions,
           LibraryPremises, DeploymentPremises, DischargedPremises,
           RegisteredGuarantees, BoundaryIds, FailureCeilings,
           GuaranteeFamily, GuaranteeKindOf, GuaranteePropertyClass,
           GuaranteeBoundaryOf, GuaranteeFailureCeilingOf,
           SupportedGuaranteeKinds, SemanticCoherence,
           ImplementationConformance)
    /\ ApplicableKernelClaims(
           SelectedFamilies,
           ObligationPremises, CheckActPremises, ProgressPremises,
           OwnershipAssurancePremises, CompositionPremises,
           RefinementPremises)

RegisteredConstructionGuaranteeBundle(
        RetainedStructures, SelectedStructures,
        Instances, StructureOf, ParameterDomain,
        ParameterDomainOf, Parameters,
        SelectedFamilies,
        RegisteredGuarantees, BoundaryIds, FailureCeilings,
        GuaranteeFamily, GuaranteeKindOf, GuaranteePropertyClass,
        GuaranteeBoundaryOf, GuaranteeFailureCeilingOf,
        SupportedGuaranteeKinds,
        ObligationConclusion, CheckActConclusion, ProgressConclusion,
        OwnershipAssuranceConclusion, CompositionConclusion,
        RefinementConclusion) ==
    /\ BuilderSelection(RetainedStructures, SelectedStructures)
    /\ BuilderInstantiation(
           SelectedStructures, Instances,
           StructureOf, ParameterDomain, ParameterDomainOf, Parameters)
    /\ GuaranteeBundleTyped(
           RegisteredGuarantees, SelectedFamilies,
           BoundaryIds, FailureCeilings,
           GuaranteeFamily, GuaranteeKindOf, GuaranteePropertyClass,
           GuaranteeBoundaryOf, GuaranteeFailureCeilingOf)
    /\ GuaranteeRegistrationCompatible(
           RegisteredGuarantees, SelectedFamilies,
           GuaranteeFamily, GuaranteeKindOf, GuaranteePropertyClass,
           SupportedGuaranteeKinds)
    /\ ApplicableKernelClaims(
           SelectedFamilies,
           ObligationConclusion, CheckActConclusion, ProgressConclusion,
           OwnershipAssuranceConclusion, CompositionConclusion,
           RefinementConclusion)

====
