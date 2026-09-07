---- MODULE IncompletePathInventory_NEG ----
EXTENDS ALKConstructionTheoremWitness

IncompleteClaimActions ==
    [claim \in Claims |-> ClaimActions[claim] \ {"fault"}]

IncompleteActionLabelInventoryHeld ==
    ExactClaimPathInventory(
        Claims, ActionLabels, IncompleteClaimActions)

UnrepresentedFormalCommitSteps ==
    GovernedCommitSteps \cup {<<"closed", "open">>}

UnrepresentedFormalCommitHeld ==
    ExactGovernedActionBoundary(
        States, Claims, Obligations, ActionLabels, PotentialActions,
        ClaimActions, AdmittedActions,
        ClaimObligations, ObligationPropertyClass,
        ViolatingActions, LivenessProgressActions,
        UnrepresentedFormalCommitSteps, ClaimCommitActions,
        GovernedActions)

CommitOmittedFromPostMediationSteps ==
    [action \in ActionLabels |->
        IF action = "commit" THEN {} ELSE PostMediationSteps[action]]

PostMediationCommitCoverageHeld ==
    KernelCommitAssuranceBinding(
        Claims, ActionLabels, PotentialActions,
        CommitOmittedFromPostMediationSteps,
        ClaimCommitActions, GuaranteeClaimant, OwnerOf, DelegateOf,
        AssuranceProviderOf, AssurancePositionOf,
        PreventionControllers, UnavailableProviders,
        PersistentEvidenceFor, RecoveryAvailableFor,
        FormalCommitSteps, FormalCommitOwner, FormalCommitDelegate,
        FormalCommitAssurance,
        KernelClaimant, KernelAssuranceProvider,
        KernelPreventionControllers, KernelUnavailableProviders,
        KernelPersistentEvidence, KernelRecoveryAvailable)

TwoCommitActions == {"commit-left", "commit-right"}
TwoCommitSteps ==
    {<<"open", "closed">>, <<"closed", "closed">>}
TwoPotentialActions ==
    [action \in TwoCommitActions |->
        IF action = "commit-left"
          THEN {<<"open", "closed">>}
          ELSE {<<"closed", "closed">>}]
AlignedTwoPostMediationSteps == TwoPotentialActions
ReassignedTwoPostMediationSteps ==
    [action \in TwoCommitActions |->
        IF action = "commit-left"
          THEN {<<"closed", "closed">>}
          ELSE {<<"open", "closed">>}]
TwoClaimCommitActions ==
    [claim \in Claims |-> TwoCommitActions]
TwoOwners == [action \in TwoCommitActions |-> "builder"]
TwoDelegates == [action \in TwoCommitActions |-> {}]
TwoProviders == [action \in TwoCommitActions |-> "assurer"]
TwoAssurancePositions ==
    [action \in TwoCommitActions |-> "at-commit"]
TwoPersistentEvidence == [action \in TwoCommitActions |-> TRUE]
TwoRecoveryAvailability == [action \in TwoCommitActions |-> TRUE]
TwoFormalCommitOwners == [step \in TwoCommitSteps |-> "builder"]
TwoFormalCommitDelegates == [step \in TwoCommitSteps |-> "builder"]
TwoFormalCommitAssurance ==
    [step \in TwoCommitSteps |-> "at-commit"]

AlignedPerActionCommitBoundaryHeld ==
    KernelCommitAssuranceBinding(
        Claims, TwoCommitActions, TwoPotentialActions,
        AlignedTwoPostMediationSteps,
        TwoClaimCommitActions, GuaranteeClaimant, TwoOwners, TwoDelegates,
        TwoProviders, TwoAssurancePositions,
        PreventionControllers, UnavailableProviders,
        TwoPersistentEvidence, TwoRecoveryAvailability,
        TwoCommitSteps, TwoFormalCommitOwners, TwoFormalCommitDelegates,
        TwoFormalCommitAssurance,
        KernelClaimant, KernelAssuranceProvider,
        KernelPreventionControllers, KernelUnavailableProviders,
        KernelPersistentEvidence, KernelRecoveryAvailable)

ReassignedPerActionCommitBoundaryHeld ==
    KernelCommitAssuranceBinding(
        Claims, TwoCommitActions, TwoPotentialActions,
        ReassignedTwoPostMediationSteps,
        TwoClaimCommitActions, GuaranteeClaimant, TwoOwners, TwoDelegates,
        TwoProviders, TwoAssurancePositions,
        PreventionControllers, UnavailableProviders,
        TwoPersistentEvidence, TwoRecoveryAvailability,
        TwoCommitSteps, TwoFormalCommitOwners, TwoFormalCommitDelegates,
        TwoFormalCommitAssurance,
        KernelClaimant, KernelAssuranceProvider,
        KernelPreventionControllers, KernelUnavailableProviders,
        KernelPersistentEvidence, KernelRecoveryAvailable)

ExternalFormalCommitDelegate ==
    [step \in FormalCommitSteps |-> "custodian"]

MismatchedCommitDelegateBoundaryHeld ==
    KernelCommitAssuranceBinding(
        Claims, ActionLabels, PotentialActions, PostMediationSteps,
        ClaimCommitActions, GuaranteeClaimant, OwnerOf, DelegateOf,
        AssuranceProviderOf, AssurancePositionOf,
        PreventionControllers, UnavailableProviders,
        PersistentEvidenceFor, RecoveryAvailableFor,
        FormalCommitSteps, FormalCommitOwner,
        ExternalFormalCommitDelegate, FormalCommitAssurance,
        KernelClaimant, KernelAssuranceProvider,
        KernelPreventionControllers, KernelUnavailableProviders,
        KernelPersistentEvidence, KernelRecoveryAvailable)

MismatchedPreventionControllerBoundaryHeld ==
    KernelCommitAssuranceBinding(
        Claims, ActionLabels, PotentialActions, PostMediationSteps,
        ClaimCommitActions, GuaranteeClaimant, OwnerOf, DelegateOf,
        AssuranceProviderOf, AssurancePositionOf,
        PreventionControllers, UnavailableProviders,
        PersistentEvidenceFor, RecoveryAvailableFor,
        FormalCommitSteps, FormalCommitOwner, FormalCommitDelegate,
        FormalCommitAssurance,
        KernelClaimant, KernelAssuranceProvider,
        {"builder"}, KernelUnavailableProviders,
        KernelPersistentEvidence, KernelRecoveryAvailable)

ExactPathInventoryHeld ==
    IncompleteActionLabelInventoryHeld
      \/ UnrepresentedFormalCommitHeld
      \/ PostMediationCommitCoverageHeld
      \/ ReassignedPerActionCommitBoundaryHeld
      \/ MismatchedCommitDelegateBoundaryHeld
      \/ MismatchedPreventionControllerBoundaryHeld

CompletePathAdjacentBoundaryHeld ==
    ExactClaimPathInventory(
        Claims, ActionLabels, ClaimActions)

NegativeControlExpected == NegativeControlGate(ExactPathInventoryHeld)

====
