---- MODULE ProfileStaleMembership_NEG ----
EXTENDS ALKProfileConcreteInstances

AdjacentMembershipChangeHeld ==
    DistributedExecutionBoundaryTyped(
        ProfileStates, ProfileMembershipOf, ProfileEpochOf,
        ProfilePartitionedStates, ProfileReconfigurationSteps,
        ProfileRetrySteps, ProfilePartitionSteps,
        ProfileRecoverySteps, ProfileCollectiveCommitSteps)

MutantUnchangedMembership ==
    [state \in ProfileStates |-> {"node-a", "node-b", "node-c"}]

MutantStaleMembershipHeld ==
    DistributedExecutionBoundaryTyped(
        ProfileStates, MutantUnchangedMembership, ProfileEpochOf,
        ProfilePartitionedStates, ProfileReconfigurationSteps,
        ProfileRetrySteps, ProfilePartitionSteps,
        ProfileRecoverySteps, ProfileCollectiveCommitSteps)

NegativeControlExpected == NegativeControlGate(MutantStaleMembershipHeld)

====
