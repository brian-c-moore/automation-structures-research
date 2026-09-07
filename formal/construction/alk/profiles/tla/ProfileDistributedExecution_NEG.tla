---- MODULE ProfileDistributedExecution_NEG ----
EXTENDS ALKProfileConcreteInstances

AdjacentDistributedExecutionHeld ==
    DistributedExecutionBoundaryTyped(
        ProfileStates, ProfileMembershipOf, ProfileEpochOf,
        ProfilePartitionedStates, ProfileReconfigurationSteps,
        ProfileRetrySteps, ProfilePartitionSteps,
        ProfileRecoverySteps, ProfileCollectiveCommitSteps)

MutantDetachedRecoverySteps == {<<"open", "reconfigured">>}

MutantDetachedRecoveryHeld ==
    DistributedExecutionBoundaryTyped(
        ProfileStates, ProfileMembershipOf, ProfileEpochOf,
        ProfilePartitionedStates, ProfileReconfigurationSteps,
        ProfileRetrySteps, ProfilePartitionSteps,
        MutantDetachedRecoverySteps, ProfileCollectiveCommitSteps)

NegativeControlExpected == NegativeControlGate(MutantDetachedRecoveryHeld)

====
