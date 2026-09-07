---- MODULE BudgetAuditKernelReconciliation_Proof ----
\* The proof reuses the concrete contract and action-partition theorems, then
\* discharges the acyclic composition-kernel interface.

EXTENDS BudgetAuditKernelReconciliation,
        BudgetAuditAssumeGuarantee_Proof,
        CompositionKernel_Proof

KernelProof == INSTANCE CompositionKernel_Proof
    WITH CompositionStateDomain <- States,
         CompositionInitialStates <- InitialStates,
         CompositionInvA <- BudgetStates,
         CompositionInvB <- AuditStates,
         CompositionStepA <- BudgetComponentSteps,
         CompositionStepB <- AuditComponentSteps,
         CompositionSharedSteps <- SharedCommitSteps,
         CompositionEnvironmentSteps <- EnvironmentSteps,
         CompositionFailureSteps <- FailureSteps,
         CompositionInterferenceSteps <- InterferenceSteps,
         CompositionRelyA <- KernelBudgetRely,
         CompositionRelyB <- KernelAuditRely,
         CompositionRelyEdges <- KernelRelyEdges,
         CompositionProviders <- Providers,
         CompositionUnavailableProviders <- UnavailableProviders

LEMMA ExistingContractReused == AGProof!Contract
  BY ConcreteContract

LEMMA ExistingPartitionReused ==
    ConcreteNoFaultStep = MappedConcreteStep
  BY ActionPartition
     DEF MappedConcreteStep, BudgetComponentSteps, AuditComponentSteps,
         SharedCommitSteps, EnvironmentSteps, FailureSteps,
         ComposedSteps, ComposedStepRel, BudgetStep, AuditStep

LEMMA InitialBudgetProof == Initializes(InitialStates, BudgetStates)
  BY SMT DEF Initializes, InitialStates, BudgetStates, States

LEMMA InitialAuditProof == Initializes(InitialStates, AuditStates)
  BY SMT DEF Initializes, InitialStates, AuditStates, States

LEMMA BudgetOwnStepProof ==
    Stable(States, BudgetStates, BudgetComponentSteps)
  BY BudgetStableProof
     DEF Stable, BudgetComponentSteps,
         AGProof!Stable, BudgetRely, AuditStep, CommitRel

LEMMA AuditOwnStepProof ==
    Stable(States, AuditStates, AuditComponentSteps)
  BY DEF Stable, AuditComponentSteps

LEMMA DirectBudgetCrossProof ==
    Stable(States, BudgetStates, AuditComponentSteps)
  BY DEF Stable, AuditComponentSteps

LEMMA AuditRelyProof ==
    /\ BudgetComponentSteps \subseteq KernelAuditRely
    /\ Stable(States, AuditStates, KernelAuditRely)
  BY AuditStableProof
     DEF Stable, BudgetComponentSteps, KernelAuditRely,
         AGProof!Stable, AuditRely, BudgetStep, AuditStep, CommitRel

LEMMA SharedCommitProof ==
    Stable(
        States, JointInvariant(BudgetStates, AuditStates),
        SharedCommitSteps)
  BY ConcreteCompositionStable
     DEF Stable, JointInvariant, SharedCommitSteps,
         AGProof!Stable, ComposedInvariantStates,
         ConcreteNoFaultStep, ComposedStepRel, BudgetStep, AuditStep,
         ReserveRel, RejectRel, CommitRel, TerminalRel

LEMMA EmptyEnvironmentProof ==
    Stable(
        States, JointInvariant(BudgetStates, AuditStates),
        EnvironmentSteps)
  BY DEF Stable, EnvironmentSteps

LEMMA EmptyFailureProof ==
    Stable(
        States, JointInvariant(BudgetStates, AuditStates),
        FailureSteps)
  BY DEF Stable, FailureSteps

LEMMA ExistingTypingReused ==
    /\ BudgetStates \subseteq States
    /\ AuditStates \subseteq States
    /\ BudgetStep \subseteq States \X States
    /\ AuditStep \subseteq States \X States
  BY WellTypedProof
     DEF AGProof!WellTyped, AGProof!Pairs

LEMMA KernelRelationTypingProof ==
    /\ RelationTyped(States, BudgetComponentSteps)
    /\ RelationTyped(States, AuditComponentSteps)
    /\ RelationTyped(States, SharedCommitSteps)
    /\ RelationTyped(States, EnvironmentSteps)
    /\ RelationTyped(States, FailureSteps)
    /\ RelationTyped(States, InterferenceSteps)
    /\ RelationTyped(States, KernelBudgetRely)
    /\ RelationTyped(States, KernelAuditRely)
  BY ExistingTypingReused
     DEF RelationTyped, Pairs,
         BudgetComponentSteps, AuditComponentSteps,
         SharedCommitSteps, EnvironmentSteps, FailureSteps,
         InterferenceSteps, KernelBudgetRely, KernelAuditRely,
         AuditStep

LEMMA BoundaryProof ==
    CompositionBoundaryPremises(
        States, InitialStates, BudgetStates, AuditStates,
        BudgetComponentSteps, AuditComponentSteps, SharedCommitSteps,
        EnvironmentSteps, FailureSteps, InterferenceSteps,
        KernelBudgetRely, KernelAuditRely,
        Providers, UnavailableProviders)
  BY ExistingTypingReused, KernelRelationTypingProof
     DEF CompositionBoundaryPremises, RelyGuaranteeTyped,
         FailureModelTyped, InitialStates,
         InterferenceSteps, SharedCommitSteps,
         BudgetComponentSteps, AuditComponentSteps,
         EnvironmentSteps, FailureSteps,
         KernelBudgetRely, KernelAuditRely,
         Providers, UnavailableProviders, ComposedSteps

LEMMA AcyclicClosureProof ==
    AcyclicSafetyClosure(
        States, InitialStates, BudgetStates, AuditStates,
        BudgetComponentSteps, AuditComponentSteps, SharedCommitSteps,
        EnvironmentSteps, FailureSteps,
        KernelBudgetRely, KernelAuditRely, KernelRelyEdges)
  BY InitialBudgetProof, InitialAuditProof,
     BudgetOwnStepProof, AuditOwnStepProof, DirectBudgetCrossProof,
     AuditRelyProof, SharedCommitProof,
     EmptyEnvironmentProof, EmptyFailureProof
     DEF AcyclicSafetyClosure, AcyclicRelyGraph,
         CrossSafetyUnderAcyclicRelies,
         CommonTransitionsPreserveJoint, KernelRelyEdges,
         PossibleRelyEdges

THEOREM ConcreteKernelPremises == KernelPremises
  BY BoundaryProof, AcyclicClosureProof
     DEF KernelPremises, CompositionSafetyPremises

LEMMA InstanceBoundaryProof ==
    KernelProof!CompositionBoundaryPremises(
        States, InitialStates, BudgetStates, AuditStates,
        BudgetComponentSteps, AuditComponentSteps, SharedCommitSteps,
        EnvironmentSteps, FailureSteps, InterferenceSteps,
        KernelBudgetRely, KernelAuditRely,
        Providers, UnavailableProviders)
  BY BoundaryProof
     DEF CompositionBoundaryPremises, RelationTyped, Pairs,
         RelyGuaranteeTyped, FailureModelTyped, ComposedSteps,
         KernelProof!CompositionBoundaryPremises,
         KernelProof!RelationTyped, KernelProof!Pairs,
         KernelProof!RelyGuaranteeTyped,
         KernelProof!FailureModelTyped,
         KernelProof!ComposedSteps

LEMMA InstanceAcyclicClosureProof ==
    KernelProof!AcyclicSafetyClosure(
        States, InitialStates, BudgetStates, AuditStates,
        BudgetComponentSteps, AuditComponentSteps, SharedCommitSteps,
        EnvironmentSteps, FailureSteps,
        KernelBudgetRely, KernelAuditRely, KernelRelyEdges)
  BY AcyclicClosureProof
     DEF AcyclicSafetyClosure, AcyclicRelyGraph, PossibleRelyEdges,
         Initializes, Stable, CrossSafetyUnderAcyclicRelies,
         CommonTransitionsPreserveJoint, JointInvariant,
         KernelProof!AcyclicSafetyClosure,
         KernelProof!AcyclicRelyGraph,
         KernelProof!PossibleRelyEdges,
         KernelProof!Initializes,
         KernelProof!Stable,
         KernelProof!CrossSafetyUnderAcyclicRelies,
         KernelProof!CommonTransitionsPreserveJoint,
         KernelProof!JointInvariant

LEMMA InstanceConclusionProof ==
    KernelProof!CompositionSafetyConclusion(
        States, InitialStates, BudgetStates, AuditStates,
        BudgetComponentSteps, AuditComponentSteps, SharedCommitSteps,
        EnvironmentSteps, FailureSteps, InterferenceSteps)
  BY InstanceBoundaryProof, InstanceAcyclicClosureProof,
     KernelProof!AcyclicCompositionSafety

THEOREM ConcreteKernelConclusion == KernelConclusion
  BY InstanceConclusionProof
     DEF KernelConclusion, CompositionSafetyConclusion,
         JointInvariant, ComposedSteps, Initializes, Stable,
         KernelProof!CompositionSafetyConclusion,
         KernelProof!JointInvariant, KernelProof!ComposedSteps,
         KernelProof!Initializes, KernelProof!Stable

THEOREM ConcreteStepPartition ==
    ConcreteNoFaultStep = MappedConcreteStep
  BY ExistingPartitionReused

====
