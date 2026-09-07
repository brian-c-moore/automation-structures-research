---- MODULE StaleEpochCommit_NEG ----
EXTENDS ALKSemanticModelWitness

StaleCollectiveCommitSteps == {<<"epoch-2", "failed-2">>}
StaleCommitDecisionMembers ==
    [pair \in StaleCollectiveCommitSteps |-> {"alk", "cluster"}]
StaleCommitEpoch == [pair \in StaleCollectiveCommitSteps |-> 1]

CurrentEpochCommit ==
    DistributedProfileBoundaryTyped(
        States, Actors, Epochs, MembershipOf, EpochOf,
        AllowedDecisionSets, StaleCollectiveCommitSteps,
        StaleCommitDecisionMembers, StaleCommitEpoch,
        PartitionedStates, ReconfigurationSteps,
        RetrySteps, RecoverySteps)

NegativeControlExpected == NegativeControlGate(CurrentEpochCommit)

====
