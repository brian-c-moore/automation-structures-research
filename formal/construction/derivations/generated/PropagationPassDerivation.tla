---- MODULE PropagationPassDerivation ----
EXTENDS PropagationPassDerivationData, TLC

PropagationRecordAccepted == DerivationRecordAccepted(Derivation)

PropagationKernelObligationPremises ==
    ObligationPreservationPremises(
        Derivation.witnessStates, Derivation.witnessInitial,
        Derivation.witnessObligationStates,
        Derivation.witnessSystemSteps,
        Derivation.witnessEnvironmentSteps,
        Derivation.witnessRelySteps)

PropagationKernelObligationConclusion ==
    ObligationPreservationConclusion(
        Derivation.witnessStates, Derivation.witnessInitial,
        Derivation.witnessObligationStates,
        Derivation.witnessSystemSteps,
        Derivation.witnessEnvironmentSteps)

PropagationKernelProgressPremises ==
    RankedProgressPremises(
        Derivation.witnessStates, Derivation.witnessActiveStates,
        Derivation.witnessClosedStates,
        Derivation.witnessProgressSteps, Derivation.witnessOtherSteps,
        Derivation.witnessRankBound, Derivation.witnessRank,
        Derivation.witnessFairnessOwners,
        Derivation.witnessFairnessOwner,
        Derivation.witnessFairnessOwnerOf)

PropagationKernelOwnershipPremises ==
    AssuranceBoundaryTyped(
        Derivation.witnessStates, Derivation.witnessActors,
        Derivation.witnessProviders, Derivation.witnessClaimant,
        Derivation.witnessCommitOwner, Derivation.witnessCommitDelegate,
        Derivation.witnessAssuranceProvider,
        Derivation.witnessAssurancePosition,
        Derivation.witnessPreventionControllers,
        Derivation.witnessFailureSteps,
        Derivation.witnessUnavailableProviders,
        Derivation.witnessPersistentObserve,
        Derivation.witnessPersistentEvidence,
        Derivation.witnessRecoveryAvailable)

PropagationKernelOwnershipConclusion ==
    OwnershipAssuranceCeiling(
        Derivation.witnessClaimant, Derivation.witnessCommitOwner,
        Derivation.witnessAssuranceProvider,
        Derivation.witnessAssurancePosition,
        Derivation.witnessPreventionControllers,
        Derivation.witnessUnavailableProviders,
        Derivation.witnessPersistentEvidence,
        Derivation.witnessRecoveryAvailable)

WrongFairnessOwnerOf ==
    [step \in Derivation.witnessProgressSteps |-> "propagation-executor"]

RejectsMisattributedFairness ==
    ~RankedProgressPremises(
        Derivation.witnessStates, Derivation.witnessActiveStates,
        Derivation.witnessClosedStates,
        Derivation.witnessProgressSteps, Derivation.witnessOtherSteps,
        Derivation.witnessRankBound, Derivation.witnessRank,
        Derivation.witnessFairnessOwners,
        Derivation.witnessFairnessOwner,
        WrongFairnessOwnerOf)

DerivationInit == progressState = "idle"
Advance ==
    \/ /\ progressState = "idle"
       /\ progressState' = "running"
    \/ /\ progressState = "running"
       /\ progressState' = "updated"
    \/ /\ progressState = "updated"
       /\ progressState' = "closed"
Other ==
    /\ progressState \in {"closed", "violating"}
    /\ UNCHANGED progressState
DerivationNext == Advance \/ Other
DerivationSpec ==
    /\ DerivationInit
    /\ [][DerivationNext]_progressVars
    /\ WF_progressVars(Advance)

PropagationEventualClosure ==
    EventualRankedClosure(Derivation.witnessClosedStates)

====
