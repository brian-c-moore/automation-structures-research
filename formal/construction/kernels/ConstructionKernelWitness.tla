---- MODULE ConstructionKernelWitness ----
EXTENDS ConstructionKernel, TLC

RetainedStructures == {"sample-structure", "sample-execution"}
SelectedStructures == RetainedStructures
RetainedExecutionCarriers == {"sample-execution"}
SelectedExecutionCarrier == "sample-execution"

Instances == {"structure-instance", "execution-instance"}
StructureOf ==
    [instance \in Instances |->
        IF instance = "structure-instance"
          THEN "sample-structure"
          ELSE "sample-execution"]
ParameterDomain == {"declared-domain"}
ParameterDomainOf ==
    [structure \in SelectedStructures |-> ParameterDomain]
Parameters == [instance \in Instances |-> "declared-domain"]

SelectedFamilies == RequiredConstructionFamilies
DeclaredGlobalAssumptions == GlobalModelingAssumptionNames
LibraryPremises ==
    GlobalModelingAssumptionNames
      \cup SelectedFamilyPremiseNames(SelectedFamilies)
DeploymentPremises == {"deployment:no-additional-rely"}
DischargedPremises == LibraryPremises \cup DeploymentPremises

RegisteredGuarantees ==
    {"safety-guarantee", "assurance-ceiling",
     "refinement-safety", "observation-evidence"}
GuaranteeFamily ==
    [guarantee \in RegisteredGuarantees |->
        CASE guarantee = "safety-guarantee" -> "obligation"
          [] guarantee = "assurance-ceiling" -> "ownership-assurance"
          [] OTHER -> "refinement"]
GuaranteeKindOf ==
    [guarantee \in RegisteredGuarantees |->
        CASE guarantee = "safety-guarantee" -> "prevention"
          [] guarantee = "assurance-ceiling" -> "conditional"
          [] OTHER -> "detection"]
GuaranteePropertyClass ==
    [guarantee \in RegisteredGuarantees |->
        IF guarantee = "observation-evidence" THEN "evidence" ELSE "safety"]
FormalStates == {"open", "closed", "bad"}
ImplementationStates == {"i-open", "i-closed", "i-bad"}
FormalInitial == {"open"}
ImplementationInitial == {"i-open"}
FormalSteps == {<<"open", "closed">>}
ImplementationSteps == {<<"i-open", "i-closed">>}
FormalCommitSteps == FormalSteps
ImplementationCommitSteps == ImplementationSteps
FormalFailureSteps == {}
ImplementationFailureSteps == {}
FormalProgressSteps == FormalSteps
ImplementationProgressSteps == ImplementationSteps
FormalEnvironmentSteps == {}
DeploymentSteps == {}
TrustedSteps == ImplementationSteps

ObservationDomain == {"open-view", "closed-view", "bad-view"}
Abstraction ==
    [state \in ImplementationStates |->
        CASE state = "i-open" -> "open"
          [] state = "i-closed" -> "closed"
          [] OTHER -> "bad"]
FormalObserve ==
    [state \in FormalStates |->
        CASE state = "open" -> "open-view"
          [] state = "closed" -> "closed-view"
          [] OTHER -> "bad-view"]
ImplementationObserve ==
    [state \in ImplementationStates |-> FormalObserve[Abstraction[state]]]

DeclaredBoundary ==
    ConstructionBoundaryId(FormalStates, FormalCommitSteps, FormalObserve)
DeclaredFailureCeiling ==
    ConstructionFailureCeilingId(FormalFailureSteps, {})
BoundaryIds == {DeclaredBoundary}
FailureCeilings == {DeclaredFailureCeiling}
GuaranteeBoundaryOf ==
    [guarantee \in RegisteredGuarantees |-> DeclaredBoundary]
GuaranteeFailureCeilingOf ==
    [guarantee \in RegisteredGuarantees |-> DeclaredFailureCeiling]

ImplementationCommitOwner ==
    [pair \in ImplementationCommitSteps |-> "builder"]
FormalCommitOwner == [pair \in FormalCommitSteps |-> "builder"]
ImplementationCommitDelegate ==
    [pair \in ImplementationCommitSteps |-> "builder"]
FormalCommitDelegate ==
    [pair \in FormalCommitSteps |-> "builder"]
ImplementationCommitAssurance ==
    [pair \in ImplementationCommitSteps |-> "at-commit"]
FormalCommitAssurance ==
    [pair \in FormalCommitSteps |-> "at-commit"]
FormalPersistentObserve ==
    [state \in FormalStates |-> state = "closed"]
ImplementationPersistentObserve ==
    [state \in ImplementationStates |->
        FormalPersistentObserve[Abstraction[state]]]

EvidenceEvents == {"close-event"}
EvidenceSubjects == {"sample-work"}
EvidenceCommitActionLinks ==
    {<<<<"open", "closed">>, <<"open", "closed">>>>}
MissingEvidenceCommitActionLinks == {}
EventObservation ==
    [event \in EvidenceEvents |-> "closed-view"]
EventSubject ==
    [event \in EvidenceEvents |-> "sample-work"]
EventAction ==
    [event \in EvidenceEvents |-> <<"open", "closed">>]
EventClaimant == [event \in EvidenceEvents |-> "builder"]
EventOwner == [event \in EvidenceEvents |-> "builder"]
EventCommit ==
    [event \in EvidenceEvents |-> <<"open", "closed">>]
EventAssurance == [event \in EvidenceEvents |-> "at-commit"]
EventEvidenceClass == [event \in EvidenceEvents |-> "evidence"]
BadEventOwner == [event \in EvidenceEvents |-> "assurer"]

KernelImplementationConformance ==
    /\ ImplementationStates # {}
    /\ FormalStates # {}
    /\ CheckableImplementationConformance(
           ImplementationStates, FormalStates,
           ImplementationInitial, FormalInitial,
           ImplementationSteps, FormalSteps,
           ImplementationCommitSteps, FormalCommitSteps,
           ImplementationFailureSteps, FormalFailureSteps,
           ImplementationProgressSteps, FormalProgressSteps,
           DeploymentSteps, FormalEnvironmentSteps,
           TrustedSteps, ObservationDomain,
           ImplementationCommitOwner, FormalCommitOwner,
           ImplementationCommitDelegate, FormalCommitDelegate,
           ImplementationCommitAssurance, FormalCommitAssurance,
           ImplementationPersistentObserve, FormalPersistentObserve,
           Abstraction, ImplementationObserve, FormalObserve)

ObligationStates == {"open", "closed"}
ObligationFamilyPremises ==
    ObligationPreservationPremises(
        FormalStates, FormalInitial, ObligationStates,
        FormalSteps, FormalEnvironmentSteps, FormalEnvironmentSteps)
ObligationFamilyConclusion ==
    ObligationPreservationConclusion(
        FormalStates, FormalInitial, ObligationStates,
        FormalSteps, FormalEnvironmentSteps)

Actors == {"builder", "assurer"}
Providers == {"assurer"}
OwnershipAssuranceFamilyPremises ==
    AssuranceBoundaryTyped(
        FormalStates, Actors, Providers,
        "builder", "builder", "builder", "assurer", "at-commit",
        {"assurer"}, FormalFailureSteps, {},
        FormalPersistentObserve, TRUE, TRUE)
OwnershipAssuranceFamilyConclusion ==
    OwnershipAssuranceCeiling(
        "builder", "builder", "assurer", "at-commit",
        {"assurer"}, {}, TRUE, TRUE)

SupportedGuaranteeKinds ==
    GuaranteeCeiling(
        "builder", "builder", "assurer", "at-commit",
        {"assurer"}, {}, TRUE, TRUE)

SelectedClasses == {"safety", "observation"}
FormalSafeStates == {"open", "closed"}
FormalObservationStates == FormalSafeStates
AllowedObservations == {"open-view", "closed-view"}
FormalClosedStates == {"closed"}
ImplementationClosedStates == {"i-closed"}
ImplementationActiveStates == ImplementationStates \ ImplementationClosedStates
FormalOtherSteps == {}
ImplementationOtherSteps == {}
RankBound == 1
FormalRank ==
    [state \in FormalStates |-> IF state = "closed" THEN 0 ELSE 1]
ImplementationRank ==
    LiftedRank(ImplementationStates, Abstraction, FormalRank)
FairnessOwners == {"executor"}
FairnessOwner == "executor"
FormalFairnessOwnerOf ==
    [step \in FormalProgressSteps |-> FairnessOwner]
ImplementationFairnessOwnerOf ==
    [step \in ImplementationProgressSteps |-> FairnessOwner]

CompositionStateDomain == FormalStates
CompositionInitialStates == FormalInitial
CompositionInvA == FormalSafeStates
CompositionInvB == FormalStates
CompositionStepA == FormalSteps
CompositionStepB == {}
CompositionSharedSteps == {}
CompositionEnvironmentSteps == FormalEnvironmentSteps
CompositionFailureSteps == FormalFailureSteps

KernelSemanticCoherence ==
    /\ StateStepBoundaryCoherence(
           SelectedFamilies,
           FormalStates, FormalInitial, FormalSteps, FormalSafeStates,
           FormalCommitSteps, FormalFailureSteps,
           FormalEnvironmentSteps,
           FormalCommitOwner, FormalCommitDelegate,
           FormalCommitAssurance, FormalPersistentObserve,
           FormalStates, FormalInitial, ObligationStates,
           FormalSteps, FormalEnvironmentSteps,
           FormalSteps \ FormalCommitSteps, FormalCommitSteps,
           FormalStates, Actors, "builder", "builder", "builder",
           FormalFailureSteps, {},
           FormalPersistentObserve, "at-commit",
           CompositionStateDomain, CompositionInitialStates,
           CompositionInvA, CompositionInvB,
           CompositionStepA, CompositionStepB,
           CompositionSharedSteps, CompositionEnvironmentSteps,
           CompositionFailureSteps, {})
    /\ ProgressRefinementCoherence(
           SelectedFamilies, SelectedClasses,
           ImplementationStates, ImplementationSteps,
           ImplementationProgressSteps, ImplementationOtherSteps,
           ImplementationClosedStates,
           FormalStates, FormalClosedStates, Abstraction)
    /\ RegistrationBoundaryCoherence(
           RegisteredGuarantees, BoundaryIds, FailureCeilings,
           GuaranteeBoundaryOf, GuaranteeFailureCeilingOf,
           FormalStates, FormalCommitSteps, FormalFailureSteps,
           FormalObserve, {})
    /\ RefinementRegistrationCoherence(
           RegisteredGuarantees, GuaranteeFamily,
           GuaranteePropertyClass, SelectedClasses)
    /\ EvidenceRegistrationCoherence(
           RegisteredGuarantees, GuaranteePropertyClass,
           SupportedGuaranteeKinds,
           EvidenceEvents, ObservationDomain, EvidenceSubjects,
           Actors, FormalSteps, FormalCommitSteps,
           EvidenceCommitActionLinks,
           EventObservation, EventSubject, EventAction,
           EventClaimant, EventOwner, EventCommit,
           EventAssurance, EventEvidenceClass,
           FormalCommitOwner, FormalCommitAssurance,
           FormalObserve, FormalPersistentObserve, "builder")

RejectsIncoherentFamilyBoundary ==
    ~StateStepBoundaryCoherence(
        SelectedFamilies,
        FormalStates, FormalInitial, FormalSteps, FormalSafeStates,
        FormalCommitSteps, FormalFailureSteps,
        FormalEnvironmentSteps,
        FormalCommitOwner, FormalCommitDelegate,
        FormalCommitAssurance, FormalPersistentObserve,
        FormalStates, FormalInitial, ObligationStates,
        FormalSteps, FormalEnvironmentSteps,
        FormalSteps \ FormalCommitSteps, FormalCommitSteps,
        {"incoherent-assurance-state"}, Actors, "builder", "builder", "builder",
        FormalFailureSteps, {},
        FormalPersistentObserve, "at-commit",
        CompositionStateDomain, CompositionInitialStates,
        CompositionInvA, CompositionInvB,
        CompositionStepA, CompositionStepB,
        CompositionSharedSteps, CompositionEnvironmentSteps,
        CompositionFailureSteps, {})

UnregisteredSelectedClasses == {"safety", "liveness", "observation"}

RejectsUnregisteredRefinementClass ==
    ~RefinementRegistrationCoherence(
        RegisteredGuarantees, GuaranteeFamily,
        GuaranteePropertyClass, UnregisteredSelectedClasses)

RejectsMisattributedEvidence ==
    ~EvidenceRegistrationCoherence(
        RegisteredGuarantees, GuaranteePropertyClass,
        SupportedGuaranteeKinds,
        EvidenceEvents, ObservationDomain, EvidenceSubjects,
        Actors, FormalSteps, FormalCommitSteps,
        EvidenceCommitActionLinks,
        EventObservation, EventSubject, EventAction,
        EventClaimant, BadEventOwner, EventCommit,
        EventAssurance, EventEvidenceClass,
        FormalCommitOwner, FormalCommitAssurance,
        FormalObserve, FormalPersistentObserve, "builder")

RejectsUnlinkedEvidence ==
    ~EvidenceRegistrationCoherence(
        RegisteredGuarantees, GuaranteePropertyClass,
        SupportedGuaranteeKinds,
        EvidenceEvents, ObservationDomain, EvidenceSubjects,
        Actors, FormalSteps, FormalCommitSteps,
        MissingEvidenceCommitActionLinks,
        EventObservation, EventSubject, EventAction,
        EventClaimant, EventOwner, EventCommit,
        EventAssurance, EventEvidenceClass,
        FormalCommitOwner, FormalCommitAssurance,
        FormalObserve, FormalPersistentObserve, "builder")

RejectsEmptyInitialConformance ==
    ~CheckableImplementationConformance(
        ImplementationStates, FormalStates,
        {}, {}, ImplementationSteps, FormalSteps,
        ImplementationCommitSteps, FormalCommitSteps,
        ImplementationFailureSteps, FormalFailureSteps,
        ImplementationProgressSteps, FormalProgressSteps,
        DeploymentSteps, FormalEnvironmentSteps,
        TrustedSteps, ObservationDomain,
        ImplementationCommitOwner, FormalCommitOwner,
        ImplementationCommitDelegate, FormalCommitDelegate,
        ImplementationCommitAssurance, FormalCommitAssurance,
        ImplementationPersistentObserve, FormalPersistentObserve,
        Abstraction, ImplementationObserve, FormalObserve)

RejectsOverlappingTrustedDeployment ==
    ~CheckableImplementationConformance(
        ImplementationStates, FormalStates,
        ImplementationInitial, FormalInitial,
        ImplementationSteps, FormalSteps,
        ImplementationCommitSteps, FormalCommitSteps,
        ImplementationFailureSteps, FormalFailureSteps,
        ImplementationProgressSteps, FormalProgressSteps,
        ImplementationSteps, FormalSteps,
        ImplementationSteps, ObservationDomain,
        ImplementationCommitOwner, FormalCommitOwner,
        ImplementationCommitDelegate, FormalCommitDelegate,
        ImplementationCommitAssurance, FormalCommitAssurance,
        ImplementationPersistentObserve, FormalPersistentObserve,
        Abstraction, ImplementationObserve, FormalObserve)

RejectsNoncheckableConformance ==
    ~CheckableImplementationConformance(
        ImplementationStates, FormalStates,
        ImplementationInitial, FormalInitial,
        ImplementationSteps, FormalSteps,
        ImplementationCommitSteps, FormalCommitSteps,
        ImplementationFailureSteps, FormalFailureSteps,
        ImplementationProgressSteps, FormalProgressSteps,
        ImplementationSteps, FormalSteps,
        ImplementationSteps, ObservationDomain,
        ImplementationCommitOwner, FormalCommitOwner,
        ImplementationCommitDelegate, FormalCommitDelegate,
        ImplementationCommitAssurance, FormalCommitAssurance,
        ImplementationPersistentObserve, FormalPersistentObserve,
        Abstraction, ImplementationObserve, FormalObserve)

RefinementFamilyPremises ==
    RefinementTransferPremises(
        SelectedClasses,
        ImplementationStates, ImplementationActiveStates,
        ImplementationClosedStates, FormalStates,
        ImplementationInitial, FormalInitial,
        ImplementationSteps, FormalSteps, FormalSafeStates,
        FormalObservationStates, ObservationDomain, AllowedObservations,
        Abstraction, ImplementationObserve, FormalObserve,
        FormalClosedStates, FormalProgressSteps, FormalOtherSteps,
        ImplementationProgressSteps, ImplementationOtherSteps,
        RankBound, FormalRank, ImplementationRank,
        FairnessOwners, FairnessOwner,
        FormalFairnessOwnerOf, ImplementationFairnessOwnerOf)
RefinementFamilyConclusion ==
    RefinementTransferConclusion(
        SelectedClasses,
        ImplementationStates, ImplementationClosedStates,
        ImplementationInitial,
        ImplementationSteps, FormalSafeStates,
        FormalObservationStates, AllowedObservations,
        Abstraction, ImplementationObserve)

SafetyRefinementPremisesHeld ==
    SafetyRefinementPremises(
        ImplementationStates, FormalStates,
        ImplementationInitial, FormalInitial,
        ImplementationSteps, FormalSteps,
        FormalSafeStates, ObservationDomain,
        Abstraction, ImplementationObserve, FormalObserve)

SafetyRefinementConclusionHeld ==
    SafetyRefinementConclusion(
        ImplementationStates, ImplementationInitial,
        ImplementationSteps, FormalSafeStates, Abstraction)

ObservationRefinementPremisesHeld ==
    ObservationPropertyPremises(
        ImplementationStates, FormalStates,
        FormalObservationStates, ObservationDomain,
        AllowedObservations, Abstraction,
        ImplementationObserve, FormalObserve)

ObservationRefinementConclusionHeld ==
    ObservationPropertyConclusion(
        ImplementationStates, FormalObservationStates,
        AllowedObservations, Abstraction, ImplementationObserve)

ConstructionStaticPremisesHeld ==
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
        SupportedGuaranteeKinds, KernelSemanticCoherence,
        KernelImplementationConformance)

ConstructionFullPremisesHeld ==
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
        SupportedGuaranteeKinds, KernelSemanticCoherence,
        KernelImplementationConformance,
        ObligationFamilyPremises, FALSE, FALSE,
        OwnershipAssuranceFamilyPremises, FALSE,
        SafetyRefinementPremisesHeld /\ ObservationRefinementPremisesHeld)

ConstructionGuaranteeHeld ==
    RegisteredConstructionGuaranteeBundle(
        RetainedStructures, SelectedStructures,
        Instances, StructureOf, ParameterDomain,
        ParameterDomainOf, Parameters,
        SelectedFamilies,
        RegisteredGuarantees, BoundaryIds, FailureCeilings,
        GuaranteeFamily, GuaranteeKindOf, GuaranteePropertyClass,
        GuaranteeBoundaryOf, GuaranteeFailureCeilingOf,
        SupportedGuaranteeKinds,
        ObligationFamilyConclusion, FALSE, FALSE,
        OwnershipAssuranceFamilyConclusion, FALSE,
        SafetyRefinementConclusionHeld /\ ObservationRefinementConclusionHeld)

Init == progressState = "i-open"

Advance ==
    /\ progressState = "i-open"
    /\ progressState' = "i-closed"

Next == Advance \/ UNCHANGED progressState

Spec == Init /\ [][Next]_progressState

====
