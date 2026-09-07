---- MODULE ALKProfilesExecutionWitness ----
EXTENDS ALKProfilesWitness

VARIABLE profileState, coveredProfileActions

ProfileExecutionVars ==
    <<phase, progressState, profileState, coveredProfileActions>>
ExpectedCoveredProfileActions ==
    {"reconfigure", "retry", "partition", "recover", "commit"}

ProfileExecutionInit ==
    /\ phase = "ready"
    /\ progressState = "open"
    /\ profileState = "open"
    /\ coveredProfileActions = {}

CoverReconfiguration ==
    /\ coveredProfileActions = {}
    /\ profileState = "open"
    /\ profileState' = "reconfigured"
    /\ coveredProfileActions' = {"reconfigure"}

CoverRetry ==
    /\ coveredProfileActions = {"reconfigure"}
    /\ profileState = "reconfigured"
    /\ profileState' = "reconfigured"
    /\ coveredProfileActions' =
         coveredProfileActions \cup {"retry"}

CoverPartition ==
    /\ coveredProfileActions = {"reconfigure", "retry"}
    /\ profileState = "reconfigured"
    /\ profileState' = "failed"
    /\ coveredProfileActions' =
         coveredProfileActions \cup {"partition"}

CoverRecovery ==
    /\ coveredProfileActions =
         {"reconfigure", "retry", "partition"}
    /\ profileState = "failed"
    /\ profileState' = "reconfigured"
    /\ coveredProfileActions' =
         coveredProfileActions \cup {"recover"}

CoverCollectiveCommit ==
    /\ coveredProfileActions =
         {"reconfigure", "retry", "partition", "recover"}
    /\ profileState = "reconfigured"
    /\ profileState' = "closed"
    /\ coveredProfileActions' =
         coveredProfileActions \cup {"commit"}

ProfileExecutionNext ==
    /\ (CoverReconfiguration \/ CoverRetry \/ CoverPartition
          \/ CoverRecovery \/ CoverCollectiveCommit)
    /\ UNCHANGED <<phase, progressState>>

ProfileExecutionSpec ==
    /\ ProfileExecutionInit
    /\ [][ProfileExecutionNext]_ProfileExecutionVars
    /\ WF_ProfileExecutionVars(ProfileExecutionNext)

ProfileExecutionTypeOK ==
    /\ profileState \in ProfileStates
    /\ coveredProfileActions \subseteq ExpectedCoveredProfileActions

ProfileExecutionUsesRegisteredRelations ==
    /\ ProfileReconfigurationSteps = {<<"open", "reconfigured">>}
    /\ ProfileRetrySteps = {<<"reconfigured", "reconfigured">>}
    /\ ProfilePartitionSteps = {<<"reconfigured", "failed">>}
    /\ ProfileRecoverySteps = {<<"failed", "reconfigured">>}
    /\ ProfileCollectiveCommitSteps = {<<"reconfigured", "closed">>}
    /\ DistributedExecutionBoundaryTyped(
           ProfileStates, ProfileMembershipOf, ProfileEpochOf,
           ProfilePartitionedStates, ProfileReconfigurationSteps,
           ProfileRetrySteps, ProfilePartitionSteps,
           ProfileRecoverySteps, ProfileCollectiveCommitSteps)

ProfileExecutionCompletes ==
    <>(/\ profileState = "closed"
       /\ coveredProfileActions = ExpectedCoveredProfileActions)

====
