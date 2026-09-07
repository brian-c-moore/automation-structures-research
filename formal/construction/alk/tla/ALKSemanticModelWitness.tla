---- MODULE ALKSemanticModelWitness ----
EXTENDS ALKSemanticModel, ALKRetainedRegistryData

\* This module inhabits the reusable ALK interface and its rejection controls.
\* Its complete registry traversal is not a deployed claim or an instantiation
\* of every catalog clause. ALKClaimInstantiationWitness supplies the bounded
\* claim frames and evaluates the selected carrier predicates directly.

VARIABLE phase

Claims == {"capacity-claim"}
Subjects == {"job"}
Scopes == {"bounded-profile"}
Actors == {"alk", "client", "store", "auditor", "cluster"}
Dependencies ==
    {"alk-code", "client-runtime", "store-service",
     "audit-key", "membership-protocol"}
FailureModels == {"named-profile-failures"}

States ==
    {"epoch-1", "committed-1", "failed-1", "partitioned-1",
     "epoch-2", "failed-2", "recovered-2", "external-failed-1"}

ActionLabels ==
    {"admit", "commit", "external-store", "bypass", "debug-path",
     "partition", "stale-epoch", "assurance-loss", "audit-loss",
     "external-owner-failure", "reconfigure", "retry", "recover"}

Actions ==
    [action \in ActionLabels |->
        CASE action = "admit" -> {<<"epoch-1", "epoch-1">>}
          [] action = "commit" -> {<<"epoch-1", "committed-1">>}
          [] action = "external-store" ->
                {<<"committed-1", "committed-1">>}
          [] action = "bypass" -> {}
          [] action = "partition" -> {<<"epoch-1", "partitioned-1">>}
          [] action = "stale-epoch" -> {<<"epoch-2", "failed-2">>}
          [] action = "assurance-loss" ->
                {<<"committed-1", "failed-1">>}
          [] action = "audit-loss" ->
                {<<"committed-1", "failed-1">>}
          [] action = "external-owner-failure" ->
                {<<"committed-1", "external-failed-1">>}
          [] action = "reconfigure" -> {<<"epoch-1", "epoch-2">>}
          [] action = "retry" ->
                {<<"partitioned-1", "partitioned-1">>}
          [] action = "recover" ->
                {<<"partitioned-1", "recovered-2">>}
          [] OTHER -> {}]

Structures == RegistryStructureNames
Connectives == RegistryConnectiveNames
ExecutionModalities == RegistryExecutionModalityNames
ObligationOccurrences ==
    RegistryObligationOccurrenceNames \cup {"seam!commit-evidence"}
Obligations ==
    RegistryNormalizedObligationNames \cup {"seam!commit-evidence"}
SeamPredicateId ==
    [path |-> "formal/construction/alk/tla/ALKSemanticModelWitness.tla",
     operator |-> "CommitEvidenceSeam"]
RegistryPredicateIds ==
    {[path |-> RegistryClausePredicatePathOf[occurrence],
      operator |-> RegistryClausePredicateOperatorOf[occurrence]] :
        occurrence \in RegistryClauseOccurrenceNames}
PredicateIds == RegistryPredicateIds \cup {SeamPredicateId}
ScopeIds == {"bounded-profile"}
ObservationBoundaryIds == {"registered-state-observation"}
FailureCeilingIds == {"named-profile-failures"}
PropertyClassesUsed == RegistryObligationPropertyClasses \cup {"relational"}
CommitBoundaryIds ==
    {"structure-commit", "execution-commit", "shared-commit"}
NormalizedKeyOf ==
    [occurrence \in ObligationOccurrences |->
        IF occurrence = "seam!commit-evidence"
          THEN occurrence
        ELSE RegistryNormalizedKeyOf[occurrence]]
PredicateOf ==
    [occurrence \in ObligationOccurrences |->
        IF occurrence = "seam!commit-evidence"
          THEN SeamPredicateId
        ELSE [path |-> RegistryClausePredicatePathOf[occurrence],
              operator |-> RegistryClausePredicateOperatorOf[occurrence]]]
ScopeOf ==
    [occurrence \in ObligationOccurrences |-> "bounded-profile"]
ObligationObservationBoundaryOf ==
    [occurrence \in ObligationOccurrences |->
        "registered-state-observation"]
ObligationFailureCeilingOf ==
    [occurrence \in ObligationOccurrences |-> "named-profile-failures"]
ObligationPropertyClassOf ==
    [occurrence \in ObligationOccurrences |->
        IF occurrence = "seam!commit-evidence"
          THEN "relational"
        ELSE RegistryObligationPropertyClassOf[occurrence]]
ObligationPropertyClass ==
    [obligation \in Obligations |->
        IF obligation = "seam!commit-evidence"
          THEN "relational"
        ELSE RegistryObligationPropertyClassOf[obligation]]
OccurrenceOwner ==
    [occurrence \in ObligationOccurrences |->
        IF occurrence = "seam!commit-evidence"
          THEN "alk"
        ELSE IF RegistryOccurrenceStructure[occurrence]
                  \in ExecutionModalities
          THEN "cluster"
        ELSE "alk"]
OccurrenceCommitBoundary ==
    [occurrence \in ObligationOccurrences |->
        IF occurrence = "seam!commit-evidence"
          THEN "shared-commit"
        ELSE IF RegistryOccurrenceStructure[occurrence]
                  \in ExecutionModalities
          THEN "execution-commit"
        ELSE "structure-commit"]
ProvedEquivalentOccurrences == {}
StructureObligationOccurrences ==
    [structure \in Structures |->
        RegistryCarrierObligationOccurrences[structure]]
ExecutionModalityObligationOccurrences ==
    [modality \in ExecutionModalities |->
        RegistryCarrierObligationOccurrences[modality]]
StructureObligations ==
    [structure \in Structures |->
        NormalizedObligations(
            StructureObligationOccurrences[structure], NormalizedKeyOf)]
ExecutionModalityObligations ==
    [modality \in ExecutionModalities |->
        NormalizedObligations(
            ExecutionModalityObligationOccurrences[modality],
            NormalizedKeyOf)]
SelectedStructures ==
    [claim \in Claims |->
        {"Budget", "ResourceRegistry", "PropagationPass", "AuditSink"}]
SelectedExecutionModality ==
    [claim \in Claims |-> "Sequential"]
CompositionSeamObligationOccurrences ==
    [claim \in Claims |-> {"seam!commit-evidence"}]
ClaimObligationOccurrences ==
    [claim \in Claims |->
        RequiredALKObligationOccurrences(
            SelectedStructures[claim],
            SelectedExecutionModality[claim],
            StructureObligationOccurrences,
            ExecutionModalityObligationOccurrences,
            CompositionSeamObligationOccurrences[claim])]

ClaimSubject == [claim \in Claims |-> "job"]
ClaimObligations ==
    [claim \in Claims |->
        RequiredALKObligations(
            SelectedStructures[claim],
            SelectedExecutionModality[claim],
            StructureObligationOccurrences,
            ExecutionModalityObligationOccurrences,
            CompositionSeamObligationOccurrences[claim],
            NormalizedKeyOf)]

SingletonSelectedStructures(structure) ==
    [claim \in Claims |-> {structure}]
OneSelectedExecutionModality(modality) ==
    [claim \in Claims |-> modality]
MatrixClaimObligationOccurrences(structure, modality) ==
    [claim \in Claims |->
        RequiredALKObligationOccurrences(
            {structure}, modality,
            StructureObligationOccurrences,
            ExecutionModalityObligationOccurrences,
            CompositionSeamObligationOccurrences[claim])]
MatrixClaimObligations(structure, modality) ==
    [claim \in Claims |->
        RequiredALKObligations(
            {structure}, modality,
            StructureObligationOccurrences,
            ExecutionModalityObligationOccurrences,
            CompositionSeamObligationOccurrences[claim],
            NormalizedKeyOf)]
RegistryConstructionMatrixSelectionHeld ==
    \A structure \in Structures, modality \in ExecutionModalities :
        ALKConstructionSelectionTyped(
            Claims, Structures, ExecutionModalities,
            ObligationOccurrences, Obligations,
            StructureObligationOccurrences,
            ExecutionModalityObligationOccurrences,
            NormalizedKeyOf,
            SingletonSelectedStructures(structure),
            OneSelectedExecutionModality(modality),
            CompositionSeamObligationOccurrences,
            MatrixClaimObligationOccurrences(structure, modality),
            MatrixClaimObligations(structure, modality))
ClaimScope == [claim \in Claims |-> "bounded-profile"]
GuaranteeClaimant == [claim \in Claims |-> "client"]
ClaimFailureModel ==
    [claim \in Claims |-> "named-profile-failures"]

SafeStates == States \ {"failed-1", "failed-2"}
ObligationStates ==
    [obligation \in Obligations |->
        IF ObligationPropertyClass[obligation] = "liveness"
          THEN States
        ELSE SafeStates]
ViolationStates ==
    [obligation \in Obligations |-> States \ ObligationStates[obligation]]
AllowedRelationSteps ==
    [obligation \in Obligations |->
        IF obligation = "seam!commit-evidence"
          THEN Pairs(States) \ {<<"committed-1", "failed-1">>}
        ELSE Pairs(States)]
ViolatingActions ==
    [obligation \in Obligations |->
        ExpectedViolatingActionsFor(
            obligation, States, ActionLabels, Actions,
            ObligationPropertyClass,
            ObligationStates, ViolationStates,
            AllowedRelationSteps)]
DerivedFrom == [obligation \in Obligations |-> {}]
LivenessActiveStates ==
    [obligation \in Obligations |-> {"epoch-1"}]
LivenessClosedStates ==
    [obligation \in Obligations |-> States \ {"epoch-1"}]
LivenessProgressActions ==
    [obligation \in Obligations |-> {"reconfigure"}]
LivenessOtherActions ==
    [obligation \in Obligations |-> ActionLabels \ {"reconfigure"}]
LivenessWeakFairProgressActions ==
    [obligation \in Obligations |-> {"reconfigure"}]
LivenessRankBound == [obligation \in Obligations |-> 1]
LivenessRank ==
    [obligation \in Obligations |->
        [state \in States |-> IF state = "epoch-1" THEN 1 ELSE 0]]
LivenessFairnessOwner ==
    [obligation \in Obligations |-> "cluster"]
LivenessFairnessOwnerOf ==
    [obligation \in Obligations |->
        [action \in ActionLabels |-> "cluster"]]

RegistryConstructionMatrixHeld ==
    /\ RegistryConstructionMatrixSelectionHeld
    /\ \A structure \in Structures, modality \in ExecutionModalities :
          SelectedObligationBoundaryTyped(
              States, ActionLabels, Actions, Claims, Obligations, Actors,
              ObligationPropertyClass,
              MatrixClaimObligations(structure, modality),
              ObligationStates, ViolationStates,
              AllowedRelationSteps, ViolatingActions,
              DerivedFrom,
              LivenessActiveStates, LivenessClosedStates,
              LivenessProgressActions, LivenessOtherActions,
              LivenessWeakFairProgressActions,
              LivenessRankBound, LivenessRank,
              LivenessFairnessOwner, LivenessFairnessOwnerOf)

ClaimActions == [claim \in Claims |-> ActionLabels]
PathClassOf ==
    [claim \in Claims |->
        [action \in ActionLabels |->
            IF action = "debug-path"
              THEN "excluded"
            ELSE IF action = "bypass"
              THEN "excluded"
            ELSE IF action \in {"external-store", "external-owner-failure"}
              THEN "external"
            ELSE "mediated"]]

AdmittedActions ==
    [claim \in Claims |-> ActionLabels \ {"debug-path", "bypass"}]
ObligationRelevantActions ==
    [claim \in Claims |->
        {"commit"}
          \cup (AdmittedActions[claim]
                  \cap SelectedGovernanceActionsFor(
                           claim, ClaimObligations,
                           ObligationPropertyClass,
                           ViolatingActions, LivenessProgressActions))]
MediatedActions ==
    [claim \in Claims |->
        MediatedActionsFor(claim, ClaimActions, PathClassOf)]
ExternalActions ==
    [claim \in Claims |->
        ExternalActionsFor(claim, ClaimActions, PathClassOf)]

OwnerOf ==
    [action \in ActionLabels |->
        IF action \in {"external-store", "external-owner-failure"}
          THEN "store"
        ELSE IF action = "bypass"
          THEN "client"
        ELSE IF action \in {"reconfigure", "retry", "recover"}
          THEN "cluster"
        ELSE "alk"]

DelegateOf ==
    [action \in ActionLabels |->
        IF action = "external-store" THEN {"store"} ELSE {}]

CommitActions == [claim \in Claims |-> {"commit"}]
ALKAuthority == [claim \in Claims |-> {"alk", "cluster"}]
ActorDependency ==
    [actor \in Actors |->
        CASE actor = "alk" -> "alk-code"
          [] actor = "client" -> "client-runtime"
          [] actor = "store" -> "store-service"
          [] actor = "auditor" -> "audit-key"
          [] OTHER -> "membership-protocol"]
ClaimTCB == [claim \in Claims |-> Dependencies]

AdmissionSteps == {<<"epoch-1", "epoch-1">>}
AuthorizedSourceStates == {"epoch-1"}
AvailableAuthorizationStates == {"epoch-1"}

EvidenceEvents == {"commit-event"}
ObservationValues == {"pending", "committed", "failed"}
EvidenceSubjects == {"job"}
EvidenceClasses == {"audit"}
EventObservation == [event \in EvidenceEvents |-> "committed"]
EventSubject == [event \in EvidenceEvents |-> "job"]
EventAction == [event \in EvidenceEvents |-> "commit"]
EventClaimant == [event \in EvidenceEvents |-> "client"]
EventOwner == [event \in EvidenceEvents |-> "alk"]
EventCommit == [event \in EvidenceEvents |-> "commit"]
EventAssurance == [event \in EvidenceEvents |-> "at-commit"]
EventEvidenceClass == [event \in EvidenceEvents |-> "audit"]
EvidenceForCommit == [action \in {"commit"} |-> EvidenceEvents]
EvidenceForObligation ==
    [obligation \in Obligations |->
        IF ObligationPropertyClass[obligation] = "evidence"
          THEN EvidenceEvents
        ELSE {}]

AdvertisedGuaranteeKinds ==
    [claim \in Claims |-> {"prevention", "detection"}]
FailureActions ==
    [claim \in Claims |->
        {"bypass", "partition", "stale-epoch", "assurance-loss",
         "audit-loss", "external-owner-failure"}]
FailureClassOf ==
    [action \in ActionLabels |->
        CASE action = "partition" -> "partition"
          [] action = "stale-epoch" -> "stale-epoch"
          [] action = "assurance-loss" -> "assurance-loss"
          [] action = "audit-loss" -> "audit-loss"
          [] action = "external-owner-failure" -> "external-owner"
          [] action = "retry" -> "retry-exhaustion"
          [] action = "recover" -> "recovery-failure"
          [] OTHER -> "bypass"]
GuaranteeUnderFailure ==
    [claim \in Claims |->
        [failureClass \in ALKFailureClasses |->
            IF failureClass = "partition"
              THEN {"conditional"}
            ELSE {"lost"}]]
AdvertisedGuaranteeUnderFailure == GuaranteeUnderFailure

Providers == {"local-log", "external-store-provider"}
EvidenceProducer == [event \in EvidenceEvents |-> "alk"]
CustodianOf == [event \in EvidenceEvents |-> "auditor"]
RetentionProviderOf ==
    [event \in EvidenceEvents |-> "external-store-provider"]
ProviderDependency ==
    [provider \in Providers |->
        IF provider = "external-store-provider"
          THEN "store-service"
        ELSE "audit-key"]
CustodyActions == {"commit", "external-store", "audit-loss"}
CustodyOwner ==
    [action \in CustodyActions |->
        IF action = "commit" THEN "alk" ELSE "store"]
CustodyFailureActions == {"audit-loss"}

Components == {"audit", "commit", "admission"}
RelyEdges ==
    {<<"audit", "commit">>, <<"commit", "audit">>,
     <<"commit", "admission">>}
RelyRank ==
    [component \in Components |->
        CASE component = "audit" -> 2
          [] component = "commit" -> 1
          [] OTHER -> 0]
RelyPropertyClassOf == [edge \in RelyEdges |-> "safety"]
DirectMutualClosureEdges ==
    {<<"audit", "commit">>, <<"commit", "audit">>}
ComponentObligationStates ==
    [component \in Components |-> SafeStates]
ComponentRelySteps ==
    [component \in Components |-> {<<"epoch-1", "epoch-1">>}]
ComponentGuaranteeSteps ==
    [component \in Components |-> {<<"epoch-1", "epoch-1">>}]
SharedStepsForRelyEdge ==
    [edge \in Components \X Components |->
        IF edge \in DirectMutualClosureEdges
          THEN {<<"epoch-1", "epoch-1">>}
        ELSE {}]

Epochs == {1, 2}
MembershipOf ==
    [state \in States |-> {"alk", "cluster"}]
EpochOf ==
    [state \in States |->
        IF state \in {"epoch-2", "failed-2", "recovered-2"}
          THEN 2
        ELSE 1]
AllowedDecisionSets ==
    [state \in States |-> {{"alk", "cluster"}}]
CollectiveCommitSteps == {<<"epoch-1", "committed-1">>}
CommitDecisionMembers ==
    [pair \in CollectiveCommitSteps |-> {"alk", "cluster"}]
CommitEpoch == [pair \in CollectiveCommitSteps |-> 1]
PartitionedStates == {"partitioned-1"}
ReconfigurationSteps == {<<"epoch-1", "epoch-2">>}
RetrySteps == {<<"partitioned-1", "partitioned-1">>}
RecoverySteps == {<<"partitioned-1", "recovered-2">>}

Observe ==
    [claim \in Claims |->
        [state \in States |->
            IF state = "committed-1"
              THEN "committed"
            ELSE IF state \in {"failed-1", "failed-2", "external-failed-1"}
              THEN "failed"
            ELSE "pending"]]
ObservationCeiling ==
    [claim \in Claims |-> {"timing", "multiplicity"}]
ResidualActions ==
    [claim \in Claims |-> {"external-store", "external-owner-failure"}]
ResidualClassOf ==
    [action \in ActionLabels |->
        IF action \in {"external-store", "external-owner-failure"}
          THEN "external-service"
        ELSE "outside-claim"]
ResidualGuaranteeCeiling ==
    [claim \in Claims |->
        [action \in ActionLabels |-> {"conditional", "lost"}]]

ModelBoundaryHolds ==
    /\ RetainedRegistryBindingTyped(
           RegistryPrimitiveNames, RegistryCompositionNames,
           RegistryConnectiveNames, RegistryExecutionModalityNames,
           RegistryObligationOccurrenceNames,
           RegistryEquivalentOccurrencePairs,
           RegistryObligationLocalNames,
           RegistryCanonicalRequirementNames,
           RegistryNormalizedObligationNames,
           RegistryObligationPropertyClasses,
           RegistryKindOf, RegistryOccurrenceStructure,
           RegistryObligationLocalNameOf,
           RegistryCanonicalRequirementNameOf,
           RegistryNormalizedKeyOf,
           RegistryObligationPropertyClassOf,
           RegistryCarrierObligationOccurrences)
    /\ RetainedConstructionBindingTyped(
           ObligationOccurrences, Structures, ExecutionModalities,
           StructureObligationOccurrences,
           ExecutionModalityObligationOccurrences,
           NormalizedKeyOf, ObligationPropertyClassOf,
           ProvedEquivalentOccurrences,
           RegistryObligationOccurrenceNames,
           RegistryEquivalentOccurrencePairs,
           RegistryCarrierObligationOccurrences,
           RegistryNormalizedKeyOf,
           RegistryObligationPropertyClassOf)
    /\ ObligationNormalizationTyped(
           ObligationOccurrences, Obligations,
           PredicateIds, ScopeIds, ObservationBoundaryIds,
           FailureCeilingIds, PropertyClassesUsed,
           Actors, CommitBoundaryIds,
           NormalizedKeyOf, PredicateOf, ScopeOf,
           ObligationObservationBoundaryOf, ObligationFailureCeilingOf,
           ObligationPropertyClassOf, ObligationPropertyClass,
           OccurrenceOwner,
           OccurrenceCommitBoundary,
           ProvedEquivalentOccurrences)
    /\ ALKKernelVocabularyTyped(
           Structures, Connectives, ExecutionModalities,
           ObligationOccurrences, Obligations,
           StructureObligationOccurrences,
           ExecutionModalityObligationOccurrences,
           NormalizedKeyOf,
           StructureObligations, ExecutionModalityObligations)
    /\ ALKConstructionSelectionTyped(
           Claims, Structures, ExecutionModalities,
           ObligationOccurrences, Obligations,
           StructureObligationOccurrences,
           ExecutionModalityObligationOccurrences,
           NormalizedKeyOf,
           SelectedStructures, SelectedExecutionModality,
           CompositionSeamObligationOccurrences,
           ClaimObligationOccurrences, ClaimObligations)
    /\ RegistryConstructionMatrixHeld
    /\ ClaimAnchorTyped(
           Claims, Subjects, Obligations, Scopes, Actors, FailureModels,
           ClaimSubject, ClaimObligations, ClaimScope,
           GuaranteeClaimant, ClaimFailureModel)
    /\ SelectedObligationBoundaryTyped(
           States, ActionLabels, Actions, Claims, Obligations, Actors,
           ObligationPropertyClass,
           ClaimObligations, ObligationStates, ViolationStates,
           AllowedRelationSteps, ViolatingActions,
           DerivedFrom,
           LivenessActiveStates, LivenessClosedStates,
           LivenessProgressActions, LivenessOtherActions,
           LivenessWeakFairProgressActions,
           LivenessRankBound, LivenessRank,
           LivenessFairnessOwner, LivenessFairnessOwnerOf)
    /\ MediationBoundaryTyped(
           States, Claims, Obligations, ActionLabels, Actions,
           ClaimActions, AdmittedActions, ClaimObligations,
           ObligationPropertyClass, ViolatingActions,
           LivenessProgressActions,
           ObligationRelevantActions, PathClassOf)
    /\ \A claim \in Claims :
          CompleteMediation(
              claim, ClaimActions, ObligationRelevantActions, PathClassOf)
    /\ ALKAuthorityBoundaryTyped(
           Claims, ActionLabels, Actors, Dependencies,
           ClaimActions, AdmittedActions,
           CommitActions, MediatedActions, ExternalActions,
           PathClassOf,
           OwnerOf, DelegateOf, ALKAuthority,
           ActorDependency, ClaimTCB)
    /\ FailSafeAdmission(
           States, AdmissionSteps, AuthorizedSourceStates,
           AvailableAuthorizationStates)
    /\ CommitEvidenceBoundaryTyped(
           {"commit"}, EvidenceEvents, ObservationValues,
           EvidenceSubjects, ActionLabels, Actors, EvidenceClasses,
           EvidenceForCommit, EventObservation, EventSubject,
           EventAction, EventClaimant, EventOwner, EventCommit,
           EventAssurance, EventEvidenceClass)
    /\ AtomicCommitEvidenceCoupled(
           {"commit"}, EvidenceForCommit, EventAssurance)
    /\ EvidenceObligationBoundaryTyped(
           Claims, Subjects, Obligations, ActionLabels, Actors, Providers,
           EvidenceEvents, CommitActions, EvidenceForCommit,
           ClaimSubject, GuaranteeClaimant, OwnerOf,
           ClaimObligations, ObligationPropertyClass,
           ClaimActions, EvidenceForObligation,
           EventSubject, EventAction, EventClaimant, EventOwner,
           EventCommit, EventAssurance,
           EvidenceProducer, CustodianOf, RetentionProviderOf)
    /\ GuaranteeFailureBoundaryTyped(
           Claims, ActionLabels, AdvertisedGuaranteeKinds,
           FailureActions, FailureClassOf, GuaranteeUnderFailure)
    /\ FailureCeilingsRespected(
           Claims, AdvertisedGuaranteeUnderFailure,
           GuaranteeUnderFailure)
    /\ CustodyBoundaryTyped(
           ActionLabels, EvidenceEvents, Actors, Providers,
           EvidenceProducer, CustodianOf, RetentionProviderOf,
           CustodyActions, CustodyOwner, CustodyFailureActions)
    /\ ClaimSpecificTCBBoundaryTyped(
           Claims, Obligations, ActionLabels, Actors,
           Dependencies, Providers,
           ClaimTCB, GuaranteeClaimant, ALKAuthority,
           AdmittedActions, ClaimObligations, ObligationPropertyClass,
           OwnerOf, DelegateOf, ActorDependency, ProviderDependency,
           EvidenceEvents, EvidenceForObligation,
           EvidenceProducer, CustodianOf, RetentionProviderOf,
           LivenessFairnessOwner)
    /\ RelyDischargeBoundaryTyped(
           States, Components, RelyEdges, RelyRank, RelyPropertyClassOf,
           DirectMutualClosureEdges,
           ComponentObligationStates,
           ComponentRelySteps, ComponentGuaranteeSteps,
           SharedStepsForRelyEdge)
    /\ DistributedProfileBoundaryTyped(
           States, Actors, Epochs, MembershipOf, EpochOf,
           AllowedDecisionSets, CollectiveCommitSteps,
           CommitDecisionMembers, CommitEpoch,
           PartitionedStates, ReconfigurationSteps,
           RetrySteps, RecoverySteps)
    /\ ObservationResidualBoundaryTyped(
           States, Claims, ActionLabels, Actors, ObservationValues,
           ClaimActions, ALKAuthority, OwnerOf, Observe,
           ObservationCeiling, ResidualActions,
           ResidualClassOf, ResidualGuaranteeCeiling)
    /\ ALKClaimBoundaryCoherent(
           Claims, ClaimActions, AdmittedActions,
           ObligationRelevantActions, ExternalActions,
           CommitActions, FailureActions, ResidualActions)

Init == phase = "ready"

Next == UNCHANGED phase

Spec == Init /\ [][Next]_phase

NegativeControlInit == Init

NegativeControlNext ==
    /\ phase = "ready"
    /\ phase' = "negative-control"

NegativeControlSpec == NegativeControlInit /\ [][NegativeControlNext]_phase

NegativeControlGate(predicate) == phase = "ready" \/ predicate

ModelWellFormed == phase = "ready" /\ ModelBoundaryHolds

====
