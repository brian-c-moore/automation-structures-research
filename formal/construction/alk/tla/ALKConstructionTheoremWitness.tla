---- MODULE ALKConstructionTheoremWitness ----
EXTENDS ALKConstructionTheorem, ALKRetainedRegistryData, TLC

\* This is a theorem-interface witness over the retained catalog inventory.
\* It does not claim that occurrence identifiers evaluate carrier semantics.
\* ALKClaimInstantiationWitness supplies the bounded semantic instantiation.

VARIABLE phase

Claims == {"bounded-claim"}
Subjects == {"work"}
Scopes == {"bounded-scope"}
Actors == {"builder", "custodian", "assurer"}
Dependencies == {"kernel-code", "audit-store", "future-adapter"}
Providers == {"assurer", "audit-provider"}

KernelClaimant == "builder"
KernelCommitOwner == "builder"
KernelCommitDelegate == "builder"
KernelAssuranceProvider == "assurer"
KernelPreventionControllers == {"assurer"}
KernelUnavailableProviders == {}
KernelPersistentEvidence == TRUE
KernelRecoveryAvailable == TRUE

States == {"open", "closed", "bad"}
ActionLabels == {"commit", "fault", "shared", "external", "bypass"}
PotentialActions ==
    [action \in ActionLabels |->
        CASE action = "commit" -> {<<"open", "closed">>}
          [] action = "fault" -> {<<"open", "bad">>}
          [] action = "shared" -> {<<"open", "open">>}
          [] action = "external" -> {<<"closed", "closed">>}
          [] OTHER -> {}]

Structures == RegistryStructureNames
ExecutionModalities == RegistryExecutionModalityNames
ObligationOccurrences == RegistryObligationOccurrenceNames
Obligations == RegistryNormalizedObligationNames
StructureObligationOccurrences ==
    [structure \in Structures |->
        RegistryCarrierObligationOccurrences[structure]]
ExecutionModalityObligationOccurrences ==
    [modality \in ExecutionModalities |->
        RegistryCarrierObligationOccurrences[modality]]
NormalizedKeyOf == RegistryNormalizedKeyOf
SelectedStructures == [claim \in Claims |-> {"Budget"}]
SelectedExecutionModality == [claim \in Claims |-> "Sequential"]
CompositionSeamObligationOccurrences == [claim \in Claims |-> {}]
ClaimObligationOccurrences ==
    [claim \in Claims |->
        RequiredALKObligationOccurrences(
            SelectedStructures[claim],
            SelectedExecutionModality[claim],
            StructureObligationOccurrences,
            ExecutionModalityObligationOccurrences,
            CompositionSeamObligationOccurrences[claim])]
ClaimObligations ==
    [claim \in Claims |->
        RequiredALKObligations(
            SelectedStructures[claim],
            SelectedExecutionModality[claim],
            StructureObligationOccurrences,
            ExecutionModalityObligationOccurrences,
            CompositionSeamObligationOccurrences[claim],
            NormalizedKeyOf)]
ObligationPropertyClass ==
    [obligation \in Obligations |->
        RegistryObligationPropertyClassOf[obligation]]
SafeStates == {"open", "closed"}
ObligationStates ==
    [obligation \in Obligations |->
        IF ObligationPropertyClass[obligation] = "liveness"
          THEN States
          ELSE SafeStates]
ViolationStates ==
    [obligation \in Obligations |-> States \ ObligationStates[obligation]]
AllowedRelationSteps ==
    [obligation \in Obligations |-> Pairs(States)]
ViolatingActions ==
    [obligation \in Obligations |->
        ExpectedViolatingActionsFor(
            obligation, States, ActionLabels, PotentialActions,
            ObligationPropertyClass, ObligationStates,
            ViolationStates, AllowedRelationSteps)]
DerivedFrom == [obligation \in Obligations |-> {}]
LivenessActiveStates == [obligation \in Obligations |-> {"open"}]
LivenessClosedStates ==
    [obligation \in Obligations |-> States \ {"open"}]
LivenessProgressActions ==
    [obligation \in Obligations |-> {"commit"}]
LivenessOtherActions ==
    [obligation \in Obligations |-> ActionLabels \ {"commit"}]
LivenessWeakFairProgressActions ==
    [obligation \in Obligations |-> {"commit"}]
LivenessRankBound == [obligation \in Obligations |-> 1]
LivenessRank ==
    [obligation \in Obligations |->
        [state \in States |-> IF state = "open" THEN 1 ELSE 0]]
LivenessFairnessOwner ==
    [obligation \in Obligations |-> "builder"]
LivenessFairnessOwnerOf ==
    [obligation \in Obligations |->
        [action \in ActionLabels |-> "builder"]]

ClaimActions == [claim \in Claims |-> ActionLabels]
PathClassOf ==
    [claim \in Claims |->
        [action \in ActionLabels |->
            IF action = "bypass"
              THEN "excluded"
              ELSE IF action = "external"
                THEN "external"
                ELSE "mediated"]]
AdmittedActions ==
    [claim \in Claims |-> ActionLabels \ {"bypass"}]
GovernedCommitSteps == PotentialActions["commit"]
ClaimCommitActions == [claim \in Claims |-> {"commit"}]
GovernedActions == [claim \in Claims |-> {"commit", "fault"}]
ObligationRelevantActions == GovernedActions
OwnerOf ==
    [action \in ActionLabels |->
        IF action = "external" THEN "custodian" ELSE "builder"]
DelegateOf == [action \in ActionLabels |-> {}]
ALKAuthority == [claim \in Claims |-> {"builder"}]

PostMediationSteps ==
    [action \in ActionLabels |->
        CASE action = "commit" -> {<<"open", "closed">>}
          [] action = "shared" -> {<<"open", "open">>}
          [] action = "external" -> {<<"closed", "closed">>}
          [] OTHER -> {}]
FormalStepsForClaim ==
    [claim \in Claims |->
        ActionUnion(AdmittedActions[claim], PostMediationSteps)]

ClaimSubject == [claim \in Claims |-> "work"]
GuaranteeClaimant == [claim \in Claims |-> KernelClaimant]
AssuranceProviderOf == [action \in ActionLabels |-> KernelAssuranceProvider]
AssurancePositionOf == [action \in ActionLabels |-> "at-commit"]
PreventionControllers == KernelPreventionControllers
UnavailableProviders == KernelUnavailableProviders
PersistentEvidenceFor ==
    [action \in ActionLabels |-> KernelPersistentEvidence]
RecoveryAvailableFor ==
    [action \in ActionLabels |-> KernelRecoveryAvailable]

EvidenceEvents == {"commit-event"}
EvidenceRequiredActions == [claim \in Claims |-> {"commit"}]
EvidenceForCommit == [action \in {"commit"} |-> EvidenceEvents]
EventSubject == [event \in EvidenceEvents |-> "work"]
EventAction == [event \in EvidenceEvents |-> "commit"]
EventClaimant == [event \in EvidenceEvents |-> "builder"]
EventOwner == [event \in EvidenceEvents |-> "builder"]
EventCommit == [event \in EvidenceEvents |-> "commit"]
EventAssurance == [event \in EvidenceEvents |-> "at-commit"]
EventObservation == [event \in EvidenceEvents |-> "closed-view"]
EventEvidenceClass == [event \in EvidenceEvents |-> "evidence"]
EvidenceProducer == [event \in EvidenceEvents |-> "builder"]
CustodianOf == [event \in EvidenceEvents |-> "custodian"]
RetentionProviderOf == [event \in EvidenceEvents |-> "audit-provider"]
EvidenceKernelEvent ==
    [event \in EvidenceEvents |-> "kernel-commit-event"]

Components == CompositionComponents
RelyEdges == {<<"component-a", "component-b">>}
RelyRank ==
    [component \in Components |->
        IF component = "component-a" THEN 1 ELSE 0]
RelyPropertyClassOf == [edge \in RelyEdges |-> "safety"]
DirectMutualClosureEdges == {}
ComponentObligationStates ==
    [component \in Components |->
        IF component = "component-a" THEN SafeStates ELSE States]
ComponentRelySteps ==
    [component \in Components |->
        IF component = "component-a"
          THEN PostMediationSteps["external"]
          ELSE {}]
ComponentGuaranteeSteps ==
    [component \in Components |->
        IF component = "component-a"
          THEN GovernedCommitSteps
          ELSE PostMediationSteps["external"]]
SharedStepsForRelyEdge ==
    [edge \in Components \X Components |-> {}]
RepresentedSharedSteps == {<<"open", "open">>}
RegisteredSharedSteps == RepresentedSharedSteps
AffectedComponents == Components

ActorDependency ==
    [actor \in Actors |->
        IF actor = "builder" THEN "kernel-code" ELSE "audit-store"]
ProviderDependency ==
    [provider \in Providers |->
        IF provider = "assurer" THEN "kernel-code" ELSE "audit-store"]
ClaimTCB == [claim \in Claims |-> Dependencies]

RetainedStructuresForKernel ==
    RetainedStructureNames \cup RetainedExecutionModalityNames
SelectedStructuresForKernel == {"Budget", "Sequential"}
RetainedExecutionCarriers == RetainedExecutionModalityNames
SelectedExecutionCarrier == "Sequential"
Instances == {"budget-instance", "sequential-instance"}
StructureOf ==
    [instance \in Instances |->
        IF instance = "budget-instance" THEN "Budget" ELSE "Sequential"]
ParameterDomain == {"bounded-parameter"}
ParameterDomainOf ==
    [structure \in SelectedStructuresForKernel |-> ParameterDomain]
Parameters == [instance \in Instances |-> "bounded-parameter"]

SelectedFamilies ==
    {"obligation", "check-act", "ownership-assurance",
     "composition", "refinement"}
DeclaredGlobalAssumptions == GlobalModelingAssumptionNames
LibraryPremises ==
    GlobalModelingAssumptionNames
      \cup SelectedFamilyPremiseNames(SelectedFamilies)
DeploymentPremises ==
    {"deployment:path-inventory", "deployment:provider-health"}
DischargedPremises == LibraryPremises \cup DeploymentPremises

RegisteredGuarantees ==
    {"obligation-safety", "check-act-license", "assurance-ceiling",
     "composition-safety", "refinement-safety", "observation-evidence"}
GuaranteeFamily ==
    [guarantee \in RegisteredGuarantees |->
        CASE guarantee = "obligation-safety" -> "obligation"
          [] guarantee = "check-act-license" -> "check-act"
          [] guarantee = "assurance-ceiling" -> "ownership-assurance"
          [] guarantee = "composition-safety" -> "composition"
          [] OTHER -> "refinement"]
GuaranteeKindOf ==
    [guarantee \in RegisteredGuarantees |->
        CASE guarantee \in {"obligation-safety", "check-act-license",
                              "composition-safety", "refinement-safety"}
          -> "prevention"
          [] guarantee = "observation-evidence" -> "detection"
          [] OTHER -> "conditional"]
GuaranteePropertyClass ==
    [guarantee \in RegisteredGuarantees |->
        IF guarantee = "observation-evidence" THEN "evidence" ELSE "safety"]
GuaranteeObligations ==
    [guarantee \in RegisteredGuarantees |->
        IF GuaranteeFamily[guarantee]
             \in {"obligation", "progress", "refinement"}
          THEN ClaimObligations["bounded-claim"]
          ELSE {}]

FormalStates == States
ImplementationStates == States
FormalInitial == {"open"}
ImplementationInitial == FormalInitial
FormalSteps == FormalStepsForClaim["bounded-claim"]
ImplementationSteps == FormalSteps
FormalCommitSteps == GovernedCommitSteps
ImplementationCommitSteps == FormalCommitSteps
FormalFailureSteps == {}
ImplementationFailureSteps == {}
FormalEnvironmentSteps == PostMediationSteps["external"]
DeploymentSteps == FormalEnvironmentSteps
TrustedSteps == FormalSteps \ FormalEnvironmentSteps
ObservationDomain == {"open-view", "closed-view", "bad-view"}
Abstraction == [state \in ImplementationStates |-> state]
FormalObserve ==
    [state \in FormalStates |->
        CASE state = "open" -> "open-view"
          [] state = "closed" -> "closed-view"
          [] OTHER -> "bad-view"]
ImplementationObserve == FormalObserve
FormalPersistentObserve ==
    [state \in FormalStates |-> state \in SafeStates]
ImplementationPersistentObserve == FormalPersistentObserve
ImplementationCommitOwner ==
    [step \in ImplementationCommitSteps |-> "builder"]
FormalCommitOwner == [step \in FormalCommitSteps |-> KernelCommitOwner]
ImplementationCommitDelegate ==
    [step \in ImplementationCommitSteps |-> KernelCommitDelegate]
FormalCommitDelegate ==
    [step \in FormalCommitSteps |-> KernelCommitDelegate]
ImplementationCommitAssurance ==
    [step \in ImplementationCommitSteps |-> "at-commit"]
FormalCommitAssurance ==
    [step \in FormalCommitSteps |-> "at-commit"]

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

KernelActors == {"builder", "assurer"}
KernelProviders == {"assurer"}
KernelAssurancePosition == "at-commit"
KernelCheckActMode == "atomic"
KernelCheckResultStates == {"open"}
KernelPredicateStates == SafeStates
KernelInterferenceSteps == FormalSteps \ FormalCommitSteps
KernelGovernedCommitSteps == FormalCommitSteps
ObligationSystemSteps == FormalSteps \ FormalEnvironmentSteps
ObligationEnvironmentSteps == FormalEnvironmentSteps
ObligationRelySteps == FormalEnvironmentSteps

ObligationFamilyPremises ==
    ObligationPreservationPremises(
        FormalStates, FormalInitial, SafeStates,
        ObligationSystemSteps, ObligationEnvironmentSteps,
        ObligationRelySteps)
ObligationFamilyConclusion ==
    ObligationPreservationConclusion(
        FormalStates, FormalInitial, SafeStates,
        ObligationSystemSteps, ObligationEnvironmentSteps)
CheckActFamilyPremises ==
    CheckActAdmission(
        FormalStates, KernelCheckActMode,
        KernelCheckResultStates, KernelPredicateStates,
        KernelInterferenceSteps, KernelGovernedCommitSteps)
CheckActFamilyConclusion ==
    CheckActLicensed(
        FormalStates, KernelPredicateStates,
        KernelGovernedCommitSteps)
OwnershipAssuranceFamilyPremises ==
    AssuranceBoundaryTyped(
        FormalStates, KernelActors, KernelProviders,
        KernelClaimant, KernelCommitOwner, KernelCommitDelegate,
        KernelAssuranceProvider, KernelAssurancePosition,
        KernelPreventionControllers, FormalFailureSteps,
        KernelUnavailableProviders, FormalPersistentObserve,
        KernelPersistentEvidence, KernelRecoveryAvailable)
OwnershipAssuranceFamilyConclusion ==
    OwnershipAssuranceCeiling(
        KernelClaimant, KernelCommitOwner, KernelAssuranceProvider,
        KernelAssurancePosition, KernelPreventionControllers,
        KernelUnavailableProviders,
        KernelPersistentEvidence, KernelRecoveryAvailable)
SupportedGuaranteeKinds ==
    GuaranteeCeiling(
        KernelClaimant, KernelCommitOwner, KernelAssuranceProvider,
        KernelAssurancePosition, KernelPreventionControllers,
        KernelUnavailableProviders,
        KernelPersistentEvidence, KernelRecoveryAvailable)

CompositionStateDomain == FormalStates
CompositionInitialStates == FormalInitial
CompositionInvA == SafeStates
CompositionInvB == FormalStates
CompositionStepA == FormalCommitSteps
CompositionStepB == PostMediationSteps["external"]
CompositionSharedSteps == RegisteredSharedSteps
CompositionEnvironmentSteps == FormalEnvironmentSteps
CompositionFailureSteps == FormalFailureSteps
CompositionInterferenceSteps ==
    CompositionSharedSteps \cup CompositionEnvironmentSteps
CompositionRelyA == PostMediationSteps["external"]
CompositionRelyB == {}
CompositionRelyEdges == RelyEdges
CompositionFamilyPremises ==
    CompositionSafetyPremises(
        CompositionStateDomain, CompositionInitialStates,
        CompositionInvA, CompositionInvB,
        CompositionStepA, CompositionStepB, CompositionSharedSteps,
        CompositionEnvironmentSteps, CompositionFailureSteps,
        CompositionInterferenceSteps,
        CompositionRelyA, CompositionRelyB, CompositionRelyEdges,
        KernelProviders, {})
CompositionFamilyConclusion ==
    CompositionSafetyConclusion(
        CompositionStateDomain, CompositionInitialStates,
        CompositionInvA, CompositionInvB,
        CompositionStepA, CompositionStepB, CompositionSharedSteps,
        CompositionEnvironmentSteps, CompositionFailureSteps,
        CompositionInterferenceSteps)

SelectedClasses == {"safety", "observation"}
FormalSafeStates == SafeStates
FormalObservationStates == SafeStates
AllowedObservations == {"open-view", "closed-view"}
FormalClosedStates == {"closed"}
ImplementationClosedStates == {"closed"}
ImplementationActiveStates == ImplementationStates \ ImplementationClosedStates
FormalProgressSteps == FormalCommitSteps
ImplementationProgressSteps == FormalProgressSteps
FormalOtherSteps == FormalSteps \ FormalProgressSteps
ImplementationOtherSteps == FormalOtherSteps
RankBound == 1
FormalRank ==
    [state \in FormalStates |-> IF state = "open" THEN 1 ELSE 0]
ImplementationRank == FormalRank
FairnessOwners == {"builder"}
FairnessOwner == "builder"
FormalFairnessOwnerOf ==
    [step \in FormalProgressSteps |-> "builder"]
ImplementationFairnessOwnerOf ==
    [step \in ImplementationProgressSteps |-> "builder"]
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
        ImplementationInitial, ImplementationSteps,
        FormalSafeStates, FormalObservationStates,
        AllowedObservations, Abstraction, ImplementationObserve)

SafetyRefinementPremisesHeld ==
    SafetyRefinementPremises(
        ImplementationStates, FormalStates,
        ImplementationInitial, FormalInitial,
        ImplementationSteps, FormalSteps,
        FormalSafeStates, ObservationDomain,
        Abstraction, ImplementationObserve, FormalObserve)
ObservationRefinementPremisesHeld ==
    ObservationPropertyPremises(
        ImplementationStates, FormalStates,
        FormalObservationStates, ObservationDomain,
        AllowedObservations, Abstraction,
        ImplementationObserve, FormalObserve)
SafetyRefinementConclusionHeld ==
    SafetyRefinementConclusion(
        ImplementationStates, ImplementationInitial,
        ImplementationSteps, FormalSafeStates, Abstraction)
ObservationRefinementConclusionHeld ==
    ObservationPropertyConclusion(
        ImplementationStates, FormalObservationStates,
        AllowedObservations, Abstraction, ImplementationObserve)

KernelEvidenceEvents == {"kernel-commit-event"}
KernelEvidenceSubjects == {"work"}
KernelEvidenceCommitActionLinks ==
    {<< <<"open", "closed">>, <<"open", "closed">> >>}
KernelEventObservation ==
    [event \in KernelEvidenceEvents |-> "closed-view"]
KernelEventSubject == [event \in KernelEvidenceEvents |-> "work"]
KernelEventAction ==
    [event \in KernelEvidenceEvents |-> <<"open", "closed">>]
KernelEventClaimant ==
    [event \in KernelEvidenceEvents |-> "builder"]
KernelEventOwner ==
    [event \in KernelEvidenceEvents |-> "builder"]
KernelEventCommit ==
    [event \in KernelEvidenceEvents |-> <<"open", "closed">>]
KernelEventAssurance ==
    [event \in KernelEvidenceEvents |-> "at-commit"]
KernelEventEvidenceClass ==
    [event \in KernelEvidenceEvents |-> "evidence"]

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

KernelSemanticCoherence ==
    /\ StateStepBoundaryCoherence(
           SelectedFamilies,
           FormalStates, FormalInitial, FormalSteps, FormalSafeStates,
           FormalCommitSteps, FormalFailureSteps, FormalEnvironmentSteps,
           FormalCommitOwner, FormalCommitDelegate,
           FormalCommitAssurance, FormalPersistentObserve,
           FormalStates, FormalInitial, SafeStates,
           ObligationSystemSteps, ObligationEnvironmentSteps,
           KernelInterferenceSteps, KernelGovernedCommitSteps,
           FormalStates, KernelActors,
           KernelClaimant, KernelCommitOwner, KernelCommitDelegate,
           FormalFailureSteps, {}, FormalPersistentObserve,
           KernelAssurancePosition,
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
           KernelEvidenceEvents, ObservationDomain,
           KernelEvidenceSubjects, KernelActors,
           FormalSteps, FormalCommitSteps,
           KernelEvidenceCommitActionLinks,
           KernelEventObservation, KernelEventSubject,
           KernelEventAction, KernelEventClaimant,
           KernelEventOwner, KernelEventCommit,
           KernelEventAssurance, KernelEventEvidenceClass,
           FormalCommitOwner, FormalCommitAssurance,
           FormalObserve, FormalPersistentObserve, KernelClaimant)

ConstructionFullPremisesHeld ==
    ConstructionAdmitted(
        RetainedStructuresForKernel, SelectedStructuresForKernel,
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
        ObligationFamilyPremises, CheckActFamilyPremises, FALSE,
        OwnershipAssuranceFamilyPremises, CompositionFamilyPremises,
        SafetyRefinementPremisesHeld /\
          ObservationRefinementPremisesHeld)

ConstructionGuaranteeHeld ==
    RegisteredConstructionGuaranteeBundle(
        RetainedStructuresForKernel, SelectedStructuresForKernel,
        Instances, StructureOf, ParameterDomain,
        ParameterDomainOf, Parameters,
        SelectedFamilies,
        RegisteredGuarantees, BoundaryIds, FailureCeilings,
        GuaranteeFamily, GuaranteeKindOf, GuaranteePropertyClass,
        GuaranteeBoundaryOf, GuaranteeFailureCeilingOf,
        SupportedGuaranteeKinds,
        ObligationFamilyConclusion, CheckActFamilyConclusion, FALSE,
        OwnershipAssuranceFamilyConclusion, CompositionFamilyConclusion,
        SafetyRefinementConclusionHeld /\
          ObservationRefinementConclusionHeld)

SelectedObligationBoundaryHeld ==
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
           Claims, Structures, ExecutionModalities,
           ObligationOccurrences, Obligations,
           StructureObligationOccurrences,
           ExecutionModalityObligationOccurrences,
           NormalizedKeyOf,
           SelectedStructures, SelectedExecutionModality,
           CompositionSeamObligationOccurrences,
           ClaimObligationOccurrences, ClaimObligations)
    /\ SelectedObligationBoundaryTyped(
           States, ActionLabels, PotentialActions,
           Claims, Obligations, Actors,
           ObligationPropertyClass,
           ClaimObligations, ObligationStates, ViolationStates,
           AllowedRelationSteps, ViolatingActions, DerivedFrom,
           LivenessActiveStates, LivenessClosedStates,
           LivenessProgressActions, LivenessOtherActions,
           LivenessWeakFairProgressActions,
           LivenessRankBound, LivenessRank,
           LivenessFairnessOwner, LivenessFairnessOwnerOf)

MediationPremisesHeld ==
    GovernedCommitMediationPremises(
        States, Claims, Obligations, ActionLabels, PotentialActions, Actors,
        ClaimActions, AdmittedActions,
        ClaimObligations, ObligationPropertyClass,
        ViolatingActions, LivenessProgressActions,
        ObligationRelevantActions, PathClassOf,
        GovernedCommitSteps, ClaimCommitActions,
        GovernedActions, OwnerOf, ALKAuthority)

MediationConclusionHeld ==
    GovernedCommitMediationConclusion(
        Claims, ClaimActions, ObligationRelevantActions,
        GovernedActions, PathClassOf)

MediationEnforcementHeld ==
    MediationEnforcementPremises(
        States, Claims, Obligations, ActionLabels,
        AdmittedActions, GovernedActions,
        ClaimObligations, ObligationStates,
        PostMediationSteps, FormalStepsForClaim)

LivenessKernelBindingHeld ==
    ExactLivenessKernelBinding(
        Claims, Obligations, ActionLabels, PotentialActions, Actors,
        ClaimObligations, ObligationPropertyClass,
        LivenessClosedStates, LivenessProgressActions,
        LivenessOtherActions, LivenessRankBound, LivenessRank,
        LivenessFairnessOwner, LivenessFairnessOwnerOf,
        SelectedFamilies,
        FormalClosedStates, FormalProgressSteps, FormalOtherSteps,
        RankBound, FormalRank, FairnessOwner, FormalFairnessOwnerOf)

CommitAssuranceInventoryHeld ==
    CommitAssuranceInventoryTyped(
        Claims, ActionLabels, Actors, Providers,
        ClaimCommitActions, GuaranteeClaimant, OwnerOf,
        AssuranceProviderOf, AssurancePositionOf,
        PreventionControllers, UnavailableProviders,
        PersistentEvidenceFor, RecoveryAvailableFor)

DerivedNormalGuaranteeBundle ==
    ResultingClaimGuaranteeBundle(
        "bounded-claim", RegisteredGuarantees, GuaranteeKindOf,
        ClaimCommitActions, GuaranteeClaimant, OwnerOf,
        AssuranceProviderOf, AssurancePositionOf,
        PreventionControllers, UnavailableProviders,
        PersistentEvidenceFor, RecoveryAvailableFor)
AdvertisedGuaranteeBundle ==
    [claim \in Claims |-> DerivedNormalGuaranteeBundle]
GuaranteeBundleHeld ==
    ClaimGuaranteeBundleMatchesDerived(
        Claims, AdvertisedGuaranteeBundle,
        RegisteredGuarantees, GuaranteeKindOf,
        ClaimCommitActions, GuaranteeClaimant, OwnerOf,
        AssuranceProviderOf, AssurancePositionOf,
        PreventionControllers, UnavailableProviders,
        PersistentEvidenceFor, RecoveryAvailableFor)

CommitEvidencePremisesHeld ==
    OwnedCommitEvidencePremises(
        States, KernelCheckActMode,
        KernelCheckResultStates, KernelPredicateStates,
        KernelInterferenceSteps, GovernedCommitSteps,
        Claims, Subjects, ActionLabels, Actors, Providers,
        EvidenceEvents, ClaimCommitActions, EvidenceRequiredActions,
        EvidenceForCommit, ClaimSubject, GuaranteeClaimant, OwnerOf,
        AssurancePositionOf,
        EventSubject, EventAction, EventClaimant, EventOwner,
        EventCommit, EventAssurance,
        EvidenceProducer, CustodianOf, RetentionProviderOf)
EvidenceRequirementBindingHeld ==
    ExactEvidenceRequirementBinding(
        Claims, ActionLabels,
        RegisteredGuarantees, GuaranteeKindOf,
        GuaranteePropertyClass,
        ClaimCommitActions, EvidenceRequiredActions)
CommitEvidenceConclusionHeld ==
    OwnedCommitEvidenceConclusion(
        States, KernelPredicateStates, GovernedCommitSteps,
        Claims, EvidenceRequiredActions, EvidenceForCommit,
        EventAssurance)

ProviderBackedRelyPremisesHeld ==
    ProviderBackedRelyPremises(
        States, Components, RelyEdges, RelyRank, RelyPropertyClassOf,
        DirectMutualClosureEdges,
        ComponentObligationStates,
        ComponentRelySteps, ComponentGuaranteeSteps,
        SharedStepsForRelyEdge, RegisteredSharedSteps)
ProviderBackedRelyConclusionHeld ==
    ProviderBackedRelyConclusion(
        Components, RelyEdges, RelyRank, RelyPropertyClassOf,
        DirectMutualClosureEdges,
        ComponentRelySteps, ComponentGuaranteeSteps)

SharedTransitionPremisesHeld ==
    SharedTransitionPremises(
        States, Components, RepresentedSharedSteps,
        RegisteredSharedSteps, AffectedComponents,
        ComponentObligationStates)

SharedTransitionConclusionHeld ==
    SharedTransitionPreservation(
        States, RegisteredSharedSteps, AffectedComponents,
        ComponentObligationStates)

FailureInputsHeld ==
    FailureInputsTyped(TRUE, TRUE, TRUE, TRUE, TRUE, TRUE, TRUE, TRUE)
BypassFailureInputBindingHeld ==
    ExactBypassFailureInputBinding(
        Claims, ActionLabels, PotentialActions,
        ClaimActions, PathClassOf, TRUE)
DerivedFailureBundle ==
    DerivedFailureGuaranteeBundle(
        DerivedNormalGuaranteeBundle,
        TRUE, TRUE, TRUE, TRUE, TRUE, TRUE, TRUE, TRUE)
AdvertisedUnderFailure == DerivedFailureBundle
FailureBundleHeld ==
    /\ NamedFailureNarrowingConclusion(
           DerivedNormalGuaranteeBundle,
           TRUE, TRUE, TRUE, TRUE, TRUE, TRUE, TRUE, TRUE)
    /\ FailureGuaranteeBundleMatchesDerived(
           AdvertisedUnderFailure, DerivedNormalGuaranteeBundle,
           TRUE, TRUE, TRUE, TRUE, TRUE, TRUE, TRUE, TRUE)

TCBClosureHeld ==
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
        ProviderDependency)
TCBRequirementGrowthBindingHeld ==
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
        {"kernel-code", "audit-store"}, {"future-adapter"})
TCBMonotonicityHeld ==
    FixedClaimTCBMonotonicity(
        Dependencies,
        {"kernel-code", "audit-store"}, {"future-adapter"})

KernelBoundaryReuseHeld ==
    /\ "check-act" \in SelectedFamilies
    /\ "composition" \in SelectedFamilies
    /\ KernelGovernedCommitSteps = FormalCommitSteps
    /\ \A claim \in Claims : FormalStepsForClaim[claim] = FormalSteps
    /\ KernelSelectionGuaranteeBinding(
           Claims, Structures, ExecutionModalities, Obligations,
           States,
           SelectedStructures, SelectedExecutionModality,
           ClaimObligations, ObligationPropertyClass, ObligationStates,
           SelectedStructuresForKernel, SelectedExecutionCarrier,
           RegisteredGuarantees, GuaranteeFamily,
           GuaranteePropertyClass, GuaranteeObligations, SafeStates)
    /\ KernelCommitAssuranceBinding(
           Claims, ActionLabels, PotentialActions, PostMediationSteps,
           ClaimCommitActions, GuaranteeClaimant, OwnerOf, DelegateOf,
           AssuranceProviderOf, AssurancePositionOf,
           PreventionControllers, UnavailableProviders,
           PersistentEvidenceFor, RecoveryAvailableFor,
           FormalCommitSteps, FormalCommitOwner, FormalCommitDelegate,
           FormalCommitAssurance,
           KernelClaimant, KernelAssuranceProvider,
           KernelPreventionControllers, KernelUnavailableProviders,
           KernelPersistentEvidence, KernelRecoveryAvailable)
    /\ KernelCompositionBinding(
           Components, RelyEdges,
           ComponentObligationStates,
           ComponentRelySteps, ComponentGuaranteeSteps,
           RegisteredSharedSteps,
           CompositionRelyEdges, CompositionInvA, CompositionInvB,
           CompositionRelyA, CompositionRelyB,
           CompositionStepA, CompositionStepB,
           CompositionSharedSteps)
    /\ KernelEvidenceBinding(
           Claims, EvidenceEvents, KernelEvidenceEvents,
           EvidenceRequiredActions, EvidenceForCommit,
           FormalCommitSteps,
           EvidenceKernelEvent,
           EventObservation,
           EventSubject, EventAction, EventClaimant, EventOwner,
           EventCommit, EventAssurance, EventEvidenceClass,
           PostMediationSteps,
           KernelEventObservation,
           KernelEventSubject, KernelEventAction,
           KernelEventClaimant, KernelEventOwner,
           KernelEventCommit, KernelEventAssurance,
           KernelEventEvidenceClass)

TheoremEntryPremisesHeld ==
    /\ SelectedObligationBoundaryHeld
    /\ ConstructionFullPremisesHeld
    /\ MediationPremisesHeld
    /\ MediationEnforcementHeld
    /\ LivenessKernelBindingHeld
    /\ CommitAssuranceInventoryHeld
    /\ EvidenceRequirementBindingHeld
    /\ CommitEvidencePremisesHeld
    /\ ProviderBackedRelyPremisesHeld
    /\ SharedTransitionPremisesHeld
    /\ FailureInputsHeld
    /\ BypassFailureInputBindingHeld
    /\ TCBClosureHeld
    /\ TCBRequirementGrowthBindingHeld
    /\ KernelBoundaryReuseHeld

TheoremEntryConclusionsHeld ==
    /\ ConstructionGuaranteeHeld
    /\ MediationConclusionHeld
    /\ GuaranteeBundleHeld
    /\ CommitEvidenceConclusionHeld
    /\ ProviderBackedRelyConclusionHeld
    /\ SharedTransitionConclusionHeld
    /\ FailureBundleHeld
    /\ TCBMonotonicityHeld

vars == <<phase, progressState>>

Init ==
    /\ phase = "ready"
    /\ progressState = "open"

Next == UNCHANGED vars

Spec == Init /\ [][Next]_vars

NegativeControlInit == Init

NegativeControlNext ==
    /\ phase = "ready"
    /\ phase' = "negative-control"
    /\ UNCHANGED progressState

NegativeControlSpec == NegativeControlInit /\ [][NegativeControlNext]_vars

NegativeControlGate(predicate) == phase = "ready" \/ predicate

====
