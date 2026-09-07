---- MODULE CompetitiveSelectionDerivation_Proof ----
EXTENDS CompetitiveSelectionDerivation, CompetitiveSelectionRanked_Proof, TLAPS

CONSTANTS HardSeats, HardNULL, SoftWeightTotal

VARIABLES HardAllocation, HardScores, SoftScores, SoftExtra

DerivationOrder == CHOOSE seq \in [1..Cardinality(Candidates) -> Candidates] :
    /\ \A c \in Candidates : \E i \in 1..Cardinality(Candidates) : seq[i] = c
    /\ \A i, j \in 1..Cardinality(Candidates) : seq[i] = seq[j] => i = j

LOCAL ObligationKernel == INSTANCE TheoryKernel_Proof WITH
    ObligationStateDomain <- Derivation.witnessStates,
    ObligationInitialStates <- Derivation.witnessInitial,
    RegisteredObligationStates <- Derivation.witnessObligationStates,
    ObligationSystemSteps <- Derivation.witnessSystemSteps,
    ObligationEnvironmentSteps <- Derivation.witnessEnvironmentSteps,
    ObligationRelySteps <- Derivation.witnessRelySteps,
    KernelCheckActMode <- Derivation.witnessCheckActMode,
    KernelCheckResultStates <- Derivation.witnessCheckResultStates,
    KernelPredicateStates <- Derivation.witnessPredicateStates,
    KernelInterferenceSteps <- Derivation.witnessInterferenceSteps,
    KernelGovernedCommitSteps <- Derivation.witnessCommitSteps

LOCAL OwnershipKernel == INSTANCE OwnershipAssuranceKernel_Proof WITH
    AssuranceStateDomain <- Derivation.witnessStates,
    AssuranceActors <- Derivation.witnessActors,
    AssuranceProviders <- Derivation.witnessProviders,
    AssuranceClaimant <- Derivation.witnessClaimant,
    AssuranceCommitOwner <- Derivation.witnessCommitOwner,
    AssuranceCommitDelegate <- Derivation.witnessCommitDelegate,
    KernelAssuranceProvider <- Derivation.witnessAssuranceProvider,
    KernelAssurancePosition <- Derivation.witnessAssurancePosition,
    KernelPreventionControllers <- Derivation.witnessPreventionControllers,
    AssuranceFailureSteps <- Derivation.witnessFailureSteps,
    AssuranceUnavailableProviders <- Derivation.witnessUnavailableProviders,
    AssurancePersistentEvidenceObserve <- Derivation.witnessPersistentObserve,
    KernelPersistentEvidence <- Derivation.witnessPersistentEvidence,
    KernelRecoveryAvailable <- Derivation.witnessRecoveryAvailable

LOCAL HardExclusiveProof == INSTANCE CompetitiveSelectionHardExclusive_Proof WITH
    Seats <- HardSeats,
    Candidates <- Candidates,
    MaxScore <- MaxScore,
    NULL <- HardNULL,
    CandidateOrder <- DerivationOrder,
    allocation <- HardAllocation,
    scores <- HardScores

LOCAL SoftMutableProof == INSTANCE CompetitiveSelectionSoftMutableScores_Proof WITH
    Candidates <- Candidates,
    WeightTotal <- SoftWeightTotal,
    MaxScore <- MaxScore,
    CandidateOrder <- DerivationOrder,
    scores <- SoftScores,
    extra <- SoftExtra

THEOREM CompetitiveSelectionLocalDischarge == Spec => []Inv
BY Safety

THEOREM CompetitiveSelectionObligationKernelDischarge ==
    ObligationKernel!ObligationPreservationPremises(
        Derivation.witnessStates, Derivation.witnessInitial,
        Derivation.witnessObligationStates, Derivation.witnessSystemSteps,
        Derivation.witnessEnvironmentSteps, Derivation.witnessRelySteps)
    => ObligationKernel!ObligationPreservationConclusion(
           Derivation.witnessStates, Derivation.witnessInitial,
           Derivation.witnessObligationStates, Derivation.witnessSystemSteps,
           Derivation.witnessEnvironmentSteps)
BY ObligationKernel!ObligationPreservation

THEOREM CompetitiveSelectionOwnershipKernelDischarge ==
    OwnershipKernel!AssuranceBoundaryTyped(
        Derivation.witnessStates, Derivation.witnessActors,
        Derivation.witnessProviders, Derivation.witnessClaimant,
        Derivation.witnessCommitOwner, Derivation.witnessCommitDelegate,
        Derivation.witnessAssuranceProvider, Derivation.witnessAssurancePosition,
        Derivation.witnessPreventionControllers, Derivation.witnessFailureSteps,
        Derivation.witnessUnavailableProviders, Derivation.witnessPersistentObserve,
        Derivation.witnessPersistentEvidence, Derivation.witnessRecoveryAvailable)
    => OwnershipKernel!OwnershipAssuranceCeiling(
           Derivation.witnessClaimant, Derivation.witnessCommitOwner,
           Derivation.witnessAssuranceProvider, Derivation.witnessAssurancePosition,
           Derivation.witnessPreventionControllers,
           Derivation.witnessUnavailableProviders,
           Derivation.witnessPersistentEvidence, Derivation.witnessRecoveryAvailable)
BY OwnershipKernel!OwnershipAssuranceClassification

THEOREM CompetitiveSelectionInstanceLocalDischarge1 == HardExclusiveProof!Safety
BY HardExclusiveProof!Safety

THEOREM CompetitiveSelectionInstanceLocalDischarge2 == SoftMutableProof!MutableScoreSafety
BY SoftMutableProof!MutableScoreSafety

THEOREM CompetitiveSelectionCheckActKernelDischarge ==
    ObligationKernel!CheckActAdmission(
        Derivation.witnessStates, Derivation.witnessCheckActMode,
        Derivation.witnessCheckResultStates, Derivation.witnessPredicateStates,
        Derivation.witnessInterferenceSteps, Derivation.witnessCommitSteps)
    => ObligationKernel!CheckActLicensed(
           Derivation.witnessStates, Derivation.witnessPredicateStates,
           Derivation.witnessCommitSteps)
BY ObligationKernel!CheckActStability

====
