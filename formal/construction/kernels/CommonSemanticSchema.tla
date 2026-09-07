---- MODULE CommonSemanticSchema ----
EXTENDS Naturals, FiniteSets

Pairs(S) == S \X S

IdentityRelation(S) == {<<s, s>> : s \in S}

GuaranteeKinds ==
    {"prevention", "detection", "recovery", "conditional", "lost"}

AssurancePositions == {"precommit", "at-commit", "postcommit", "none"}

PropertyClasses == {"safety", "liveness", "relational", "evidence"}

GlobalModelingAssumptionNames ==
    {"atomic-interleaving", "shared-step-atomicity",
     "declared-failures", "logical-time",
     "stuttering-without-progress-credit", "registered-observation",
     "linearizable-refinement-boundary",
     "parametric-proof-or-declared-finite-bound"}

RelationTyped(S, Rel) == Rel \subseteq Pairs(S)

ActionFamilyTyped(S, ActionLabels, Actions) ==
    Actions \in [ActionLabels -> SUBSET Pairs(S)]

ActionUnion(ActionLabels, Actions) ==
    UNION {Actions[label] : label \in ActionLabels}

SystemTransition(S, AdmittedLabels, EnvironmentLabels, Actions) ==
    /\ ActionFamilyTyped(
           S, AdmittedLabels \cup EnvironmentLabels, Actions)
    /\ ActionUnion(AdmittedLabels \cup EnvironmentLabels, Actions)
         \subseteq Pairs(S)

ObligationTyped(S, ObligationStates, ViolationStates,
                Claimants, Claimant) ==
    /\ ObligationStates \subseteq S
    /\ ViolationStates = S \ ObligationStates
    /\ Claimant \in Claimants

OwnershipBoundaryTyped(ActionLabels, Actors, OwnerOf, DelegateOf,
                       CommitActions, AssuranceAt) ==
    /\ OwnerOf \in [ActionLabels -> Actors]
    /\ DelegateOf \in [ActionLabels -> SUBSET Actors]
    /\ CommitActions \subseteq ActionLabels
    /\ AssuranceAt \in [CommitActions -> AssurancePositions]

RelyGuaranteeTyped(S, RelySteps, GuaranteeSteps) ==
    /\ RelationTyped(S, RelySteps)
    /\ RelationTyped(S, GuaranteeSteps)

FailureModelTyped(S, FailureSteps, UnavailableProviders, Providers) ==
    /\ RelationTyped(S, FailureSteps)
    /\ UnavailableProviders \subseteq Providers

GuaranteeRegistrationTyped(GuaranteeKind, PropertyClass,
                           ObservationDomain, Observe) ==
    /\ GuaranteeKind \in GuaranteeKinds
    /\ PropertyClass \in PropertyClasses
    /\ DOMAIN Observe # {}
    /\ ObservationDomain = {Observe[s] : s \in DOMAIN Observe}

ProgressMeasureTyped(S, ClosedStates, RankBound, Rank) ==
    /\ ClosedStates \subseteq S
    /\ RankBound \in Nat
    /\ Rank \in [S -> 0..RankBound]
    /\ ClosedStates = {s \in S : Rank[s] = 0}

PersistentAcross(S, PersistentObserve, FailureSteps) ==
    /\ DOMAIN PersistentObserve = S
    /\ RelationTyped(S, FailureSteps)
    /\ \A pair \in FailureSteps :
          PersistentObserve[pair[2]] = PersistentObserve[pair[1]]

ExecutionProfileTyped(S, ActiveStates, ClosedStates,
                      ProgressSteps, HandoffSteps, FailureSteps,
                      PersistentObserve) ==
    /\ ActiveStates \subseteq S
    /\ ClosedStates \subseteq S
    /\ RelationTyped(S, ProgressSteps)
    /\ RelationTyped(S, HandoffSteps)
    /\ PersistentAcross(S, PersistentObserve, FailureSteps)

EvidenceProfileTyped(EvidenceEvents, ObservationDomain,
                     Subjects, Actions, Actors, CommitIds,
                     EvidenceClasses, EventObservation,
                     EventSubject, EventAction, EventClaimant,
                     EventOwner, EventCommit, EventAssurance,
                     EventEvidenceClass) ==
    /\ EventObservation \in [EvidenceEvents -> ObservationDomain]
    /\ EventSubject \in [EvidenceEvents -> Subjects]
    /\ EventAction \in [EvidenceEvents -> Actions]
    /\ EventClaimant \in [EvidenceEvents -> Actors]
    /\ EventOwner \in [EvidenceEvents -> Actors]
    /\ EventCommit \in [EvidenceEvents -> CommitIds]
    /\ EventAssurance \in [EvidenceEvents -> AssurancePositions]
    /\ EventEvidenceClass \in [EvidenceEvents -> EvidenceClasses]

CompositionBoundaryTyped(S, ComponentSteps, SharedSteps,
                         EnvironmentSteps, InterferenceSteps) ==
    /\ RelationTyped(S, ComponentSteps)
    /\ RelationTyped(S, SharedSteps)
    /\ RelationTyped(S, EnvironmentSteps)
    /\ RelationTyped(S, InterferenceSteps)
    /\ InterferenceSteps \subseteq ComponentSteps \cup EnvironmentSteps

Stable(S, PredicateStates, Rel) ==
    \A s \in PredicateStates, t \in S :
        <<s, t>> \in Rel => t \in PredicateStates

Initializes(InitialStates, PredicateStates) ==
    InitialStates \subseteq PredicateStates

PeerReliesDischarged(S, StepA, StepB, RelyA, RelyB) ==
    /\ RelationTyped(S, StepA)
    /\ RelationTyped(S, StepB)
    /\ RelationTyped(S, RelyA)
    /\ RelationTyped(S, RelyB)
    /\ StepA \subseteq RelyB
    /\ StepB \subseteq RelyA

MutualSafetyClosure(S, InitialStates, InvariantStates,
                    StepA, StepB, SharedSteps, EnvironmentSteps) ==
    /\ InitialStates \subseteq S
    /\ InvariantStates \subseteq S
    /\ RelationTyped(S, StepA)
    /\ RelationTyped(S, StepB)
    /\ RelationTyped(S, SharedSteps)
    /\ RelationTyped(S, EnvironmentSteps)
    /\ Initializes(InitialStates, InvariantStates)
    /\ Stable(S, InvariantStates, StepA)
    /\ Stable(S, InvariantStates, StepB)
    /\ Stable(S, InvariantStates, SharedSteps)
    /\ Stable(S, InvariantStates, EnvironmentSteps)

AdmittedMutualComposition(S, InitialStates, InvariantStates,
                          StepA, StepB, SharedSteps, EnvironmentSteps,
                          RelyA, RelyB) ==
    /\ PeerReliesDischarged(S, StepA, StepB, RelyA, RelyB)
    /\ MutualSafetyClosure(S, InitialStates, InvariantStates,
                           StepA, StepB, SharedSteps, EnvironmentSteps)

MappedPair(Abstraction, pair) ==
    <<Abstraction[pair[1]], Abstraction[pair[2]]>>

InitialStatesRefine(ImplementationInitial, FormalInitial, Abstraction) ==
    \A i \in ImplementationInitial : Abstraction[i] \in FormalInitial

StepsRefine(ImplementationSteps, FormalStates, FormalSteps, Abstraction) ==
    \A pair \in ImplementationSteps :
        MappedPair(Abstraction, pair)
            \in FormalSteps \cup IdentityRelation(FormalStates)

StepsRefineWithoutStutter(ImplementationSteps, FormalSteps, Abstraction) ==
    \A pair \in ImplementationSteps :
        MappedPair(Abstraction, pair) \in FormalSteps

ObservationsAgree(ImplementationStates, ImplementationObserve,
                  FormalObserve, Abstraction) ==
    \A i \in ImplementationStates :
        ImplementationObserve[i] = FormalObserve[Abstraction[i]]

FunctionalConformance(ImplementationStates, FormalStates,
                      ImplementationInitial, FormalInitial,
                      ImplementationSteps, FormalSteps,
                      ObservationDomain, Abstraction,
                      ImplementationObserve, FormalObserve) ==
    /\ ImplementationInitial \subseteq ImplementationStates
    /\ FormalInitial \subseteq FormalStates
    /\ RelationTyped(ImplementationStates, ImplementationSteps)
    /\ RelationTyped(FormalStates, FormalSteps)
    /\ Abstraction \in [ImplementationStates -> FormalStates]
    /\ ImplementationObserve \in [ImplementationStates -> ObservationDomain]
    /\ FormalObserve \in [FormalStates -> ObservationDomain]
    /\ InitialStatesRefine(ImplementationInitial, FormalInitial, Abstraction)
    /\ StepsRefine(ImplementationSteps, FormalStates, FormalSteps, Abstraction)
    /\ ObservationsAgree(ImplementationStates, ImplementationObserve,
                         FormalObserve, Abstraction)

CommitFailureConformance(ImplementationStates, FormalStates,
                         ImplementationSteps, FormalSteps,
                         ImplementationCommitSteps, FormalCommitSteps,
                         ImplementationFailureSteps, FormalFailureSteps,
                         Abstraction) ==
    /\ RelationTyped(ImplementationStates, ImplementationSteps)
    /\ RelationTyped(FormalStates, FormalSteps)
    /\ RelationTyped(ImplementationStates, ImplementationCommitSteps)
    /\ RelationTyped(FormalStates, FormalCommitSteps)
    /\ RelationTyped(ImplementationStates, ImplementationFailureSteps)
    /\ RelationTyped(FormalStates, FormalFailureSteps)
    /\ FormalCommitSteps \subseteq FormalSteps
    /\ FormalFailureSteps \subseteq FormalSteps
    /\ ImplementationCommitSteps =
         {pair \in ImplementationSteps :
             MappedPair(Abstraction, pair) \in FormalCommitSteps}
    /\ ImplementationFailureSteps =
         {pair \in ImplementationSteps :
             MappedPair(Abstraction, pair) \in FormalFailureSteps}
    /\ StepsRefineWithoutStutter(
           ImplementationCommitSteps, FormalCommitSteps, Abstraction)
    /\ StepsRefineWithoutStutter(
           ImplementationFailureSteps, FormalFailureSteps, Abstraction)

CommitBoundaryConformance(ImplementationCommitSteps, FormalCommitSteps,
                          ImplementationCommitOwner, FormalCommitOwner,
                          ImplementationCommitDelegate, FormalCommitDelegate,
                          ImplementationCommitAssurance,
                          FormalCommitAssurance, Abstraction) ==
    /\ DOMAIN ImplementationCommitOwner = ImplementationCommitSteps
    /\ DOMAIN FormalCommitOwner = FormalCommitSteps
    /\ DOMAIN ImplementationCommitDelegate = ImplementationCommitSteps
    /\ DOMAIN FormalCommitDelegate = FormalCommitSteps
    /\ DOMAIN ImplementationCommitAssurance = ImplementationCommitSteps
    /\ DOMAIN FormalCommitAssurance = FormalCommitSteps
    /\ \A pair \in ImplementationCommitSteps :
          /\ MappedPair(Abstraction, pair) \in FormalCommitSteps
          /\ ImplementationCommitOwner[pair]
               = FormalCommitOwner[MappedPair(Abstraction, pair)]
          /\ ImplementationCommitDelegate[pair]
               = FormalCommitDelegate[MappedPair(Abstraction, pair)]
          /\ ImplementationCommitAssurance[pair]
               = FormalCommitAssurance[MappedPair(Abstraction, pair)]

DeploymentRelyDischarged(ImplementationStates, DeploymentSteps,
                         FormalStates, FormalEnvironmentSteps,
                         Abstraction) ==
    /\ RelationTyped(ImplementationStates, DeploymentSteps)
    /\ RelationTyped(FormalStates, FormalEnvironmentSteps)
    /\ StepsRefine(DeploymentSteps, FormalStates,
                   FormalEnvironmentSteps, Abstraction)

TrustedBoundaryClosed(ImplementationStates, ImplementationSteps,
                      TrustedSteps, DeploymentSteps) ==
    /\ RelationTyped(ImplementationStates, ImplementationSteps)
    /\ RelationTyped(ImplementationStates, TrustedSteps)
    /\ RelationTyped(ImplementationStates, DeploymentSteps)
    /\ ImplementationSteps = TrustedSteps \cup DeploymentSteps
    /\ TrustedSteps \cap DeploymentSteps = {}

ProgressStepsRefineWithoutStutter(ImplementationProgressSteps,
                                  FormalProgressSteps, Abstraction) ==
    StepsRefineWithoutStutter(
        ImplementationProgressSteps, FormalProgressSteps, Abstraction)

PersistenceConformance(ImplementationStates, FormalStates,
                       ImplementationPersistentObserve,
                       FormalPersistentObserve, Abstraction) ==
    /\ DOMAIN ImplementationPersistentObserve = ImplementationStates
    /\ DOMAIN FormalPersistentObserve = FormalStates
    /\ \A i \in ImplementationStates :
          ImplementationPersistentObserve[i]
            = FormalPersistentObserve[Abstraction[i]]

CheckableImplementationConformance(
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
        Abstraction, ImplementationObserve, FormalObserve) ==
    /\ ImplementationInitial # {}
    /\ FormalInitial # {}
    /\ ImplementationSteps # {}
    /\ FormalSteps # {}
    /\ ImplementationCommitSteps # {}
    /\ FormalCommitSteps # {}
    /\ FunctionalConformance(
           ImplementationStates, FormalStates,
           ImplementationInitial, FormalInitial,
           ImplementationSteps, FormalSteps,
           ObservationDomain, Abstraction,
           ImplementationObserve, FormalObserve)
    /\ CommitFailureConformance(
           ImplementationStates, FormalStates,
           ImplementationSteps, FormalSteps,
           ImplementationCommitSteps, FormalCommitSteps,
           ImplementationFailureSteps, FormalFailureSteps, Abstraction)
    /\ ImplementationCommitSteps \subseteq ImplementationSteps
    /\ FormalCommitSteps \subseteq FormalSteps
    /\ ImplementationFailureSteps \subseteq ImplementationSteps
    /\ FormalFailureSteps \subseteq FormalSteps
    /\ ImplementationProgressSteps \subseteq ImplementationSteps
    /\ FormalProgressSteps \subseteq FormalSteps
    /\ CommitBoundaryConformance(
           ImplementationCommitSteps, FormalCommitSteps,
           ImplementationCommitOwner, FormalCommitOwner,
           ImplementationCommitDelegate, FormalCommitDelegate,
           ImplementationCommitAssurance, FormalCommitAssurance,
           Abstraction)
    /\ DeploymentRelyDischarged(
           ImplementationStates, DeploymentSteps,
           FormalStates, FormalEnvironmentSteps, Abstraction)
    /\ TrustedBoundaryClosed(
           ImplementationStates, ImplementationSteps,
           TrustedSteps, DeploymentSteps)
    /\ ProgressStepsRefineWithoutStutter(
           ImplementationProgressSteps, FormalProgressSteps, Abstraction)
    /\ PersistenceConformance(
           ImplementationStates, FormalStates,
           ImplementationPersistentObserve,
           FormalPersistentObserve, Abstraction)
    /\ PersistentAcross(
           FormalStates, FormalPersistentObserve, FormalFailureSteps)
    /\ PersistentAcross(
           ImplementationStates, ImplementationPersistentObserve,
           ImplementationFailureSteps)

BuilderSelection(RetainedStructures, SelectedStructures) ==
    SelectedStructures \subseteq RetainedStructures

BuilderInstantiation(SelectedStructures, Instances,
                     StructureOf, ParameterDomain,
                     ParameterDomainOf, Parameters) ==
    /\ StructureOf \in [Instances -> SelectedStructures]
    /\ ParameterDomainOf
         \in [SelectedStructures -> SUBSET ParameterDomain]
    /\ Parameters \in [Instances -> ParameterDomain]
    /\ \A instance \in Instances :
          Parameters[instance]
            \in ParameterDomainOf[StructureOf[instance]]
    /\ SelectedStructures =
         {StructureOf[instance] : instance \in Instances}

PremiseBoundary(LibraryPremises, DeploymentPremises,
                DischargedPremises) ==
    /\ LibraryPremises \cap DeploymentPremises = {}
    /\ LibraryPremises \cup DeploymentPremises
         \subseteq DischargedPremises

ConcreteSafeStates(ImplementationStates, FormalSafeStates, Abstraction) ==
    {i \in ImplementationStates : Abstraction[i] \in FormalSafeStates}

====
