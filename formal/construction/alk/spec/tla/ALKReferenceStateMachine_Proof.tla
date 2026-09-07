----------------- MODULE ALKReferenceStateMachine_Proof -----------------
EXTENDS ALKReferenceStateMachine, TLAPS

THEOREM AtomicCommitPublishesOneDurableEffectAndEvidence ==
    CommitAtomic =>
      /\ phase' = "committed"
      /\ effectCount' = 1
      /\ effectOwner' = configuredOwner
      /\ effectDurable'
      /\ evidenceState' = "durable"
      /\ custodyState' = "custodian"
      /\ clientResponse' = "success"
BY SMT DEF CommitAtomic

THEOREM PartialPersistenceCannotReportSuccess ==
    ApplyEffectBeforeEvidence =>
      /\ phase' = "recovering"
      /\ effectCount' = 1
      /\ effectOwner' = configuredOwner
      /\ effectDurable'
      /\ evidenceState' = "pending"
      /\ custodyState' = "producer"
      /\ recoveryIntent'
      /\ clientResponse' = "lost"
BY SMT DEF ApplyEffectBeforeEvidence

THEOREM RecoveryCompletesEvidenceWithoutASecondEffect ==
    RecoverEvidence =>
      /\ phase' = "committed"
      /\ effectCount' = effectCount
      /\ effectCount' = 1
      /\ effectOwner' = effectOwner
      /\ evidenceState' = "durable"
      /\ custodyState' = "custodian"
      /\ ~recoveryIntent'
      /\ clientResponse' = "success"
BY SMT DEF RecoverEvidence

THEOREM RetryExhaustionIsARejectionBeforeEffect ==
    FailBeforeEffect /\ attempts + 1 = MaxAttempts =>
      /\ phase' = "rejected"
      /\ effectCount' = effectCount
      /\ clientResponse' = "rejected"
      /\ lastFailure' = "retry-exhaustion"
BY SMT DEF FailBeforeEffect

THEOREM SameRequestDuplicateReturnsPriorSuccessWithoutEffect ==
    (DuplicateSameRequest /\ PresentedEpochUpdate) =>
      /\ phase' = phase
      /\ effectCount' = effectCount
      /\ evidenceState' = evidenceState
      /\ presentedDigest' = requestDigest
      /\ presentedEpoch' = requestEpoch'
      /\ presentedOrder' = requestOrder
      /\ clientResponse' = "success"
BY SMT DEF DuplicateSameRequest, PresentedEpochUpdate

THEOREM ConflictingDuplicateUsesADistinctPresentedDigest ==
    (ConflictingDuplicate /\ PresentedEpochUpdate) =>
      /\ presentedDigest' # requestDigest'
      /\ presentedEpoch' = requestEpoch'
      /\ presentedOrder' = requestOrder'
      /\ effectCount' = effectCount
      /\ clientResponse' = "conflict"
BY SMT DEF ConflictingDuplicate, PresentedEpochUpdate

THEOREM ConflictingDuplicateCannotCreateAnEffect ==
    ConflictingDuplicate =>
      /\ phase' = phase
      /\ effectCount' = effectCount
      /\ clientResponse' = "conflict"
BY SMT DEF ConflictingDuplicate

THEOREM LostResponseRetryIsIdempotent ==
    (RetryLostResponse /\ PresentedEpochUpdate) =>
      /\ effectCount' = effectCount
      /\ evidenceState' = evidenceState
      /\ presentedEpoch' = requestEpoch'
      /\ clientResponse' = "success"
BY SMT DEF RetryLostResponse, PresentedEpochUpdate

THEOREM StaleReplayCannotStartAnOperation ==
    (ReplayStaleRequest /\ PresentedEpochUpdate /\ ConfigurationEpochBound) =>
      /\ phase' = phase
      /\ operationId' = operationId
      /\ effectCount' = effectCount
      /\ presentedEpoch' = 1
      /\ presentedEpoch' < epoch'
      /\ clientResponse' = "stale"
      /\ lastFailure' = "stale-epoch"
BY SMT DEF ReplayStaleRequest, PresentedEpochUpdate, ConfigurationEpochBound,
           configVars

THEOREM ReorderedRequestCannotCreateAnEffect ==
    (RejectReorderedRequest /\ PresentedEpochUpdate) =>
      /\ phase' = phase
      /\ effectCount' = effectCount
      /\ evidenceState' = evidenceState
      /\ presentedDigest' = requestDigest'
      /\ presentedEpoch' = requestEpoch'
      /\ presentedOrder' < requestOrder'
      /\ clientResponse' = "stale"
      /\ lastFailure' = "reordered"
BY SMT DEF RejectReorderedRequest, PresentedEpochUpdate

THEOREM SameRequestAndResponseRetryPreservePresentedIdentity ==
    ((DuplicateSameRequest \/ RetryLostResponse) /\ PresentedEpochUpdate) =>
      /\ presentedDigest' = requestDigest'
      /\ presentedEpoch' = requestEpoch'
      /\ presentedOrder' = requestOrder'
      /\ effectCount' = effectCount
BY SMT DEF DuplicateSameRequest, RetryLostResponse, PresentedEpochUpdate

THEOREM GovernedUpdateChangesEveryClaimBearingRevisionAndEpoch ==
    (GovernedConfigurationUpdate
      /\ OwnerConfigurationBound
      /\ GuaranteeConfigurationBound
      /\ TCBConfigurationBound) =>
      /\ configVersion' = 2
      /\ ownerRevision' = configVersion'
      /\ guaranteeRevision' = configVersion'
      /\ tcbRevision' = configVersion'
      /\ epoch' = configVersion'
      /\ credentialEpoch' = epoch'
      /\ membership' = MembershipFor(Profile, configVersion')
      /\ configuredOwner' = ConfiguredOwnerFor(Profile, configVersion')
      /\ configuredGuarantees' =
           ConfiguredGuaranteesFor(
             Profile, AssuranceMode, configVersion')
      /\ configuredTCB' = ConfiguredTCBFor(Profile, configVersion')
      /\ configuredOwner' # configuredOwner
      /\ configuredGuarantees' # configuredGuarantees
      /\ configuredTCB' # configuredTCB
BY SMT DEF GovernedConfigurationUpdate, OwnerConfigurationBound,
           GuaranteeConfigurationBound, TCBConfigurationBound,
           ConfiguredOwnerFor, ConfiguredGuaranteesFor,
           UpdatedGuarantees, AdvertisedGuarantees, HealthyNormalBundle,
           ConfiguredTCBFor, RequiredTCB, BaseRequiredTCB

THEOREM CrashBeforeCheckHasNoOperationOrEffect ==
    CrashBeforeCheck =>
      /\ phase' = phase
      /\ operationId' = operationId
      /\ effectCount' = effectCount
      /\ crashed'
BY SMT DEF CrashBeforeCheck, operationVars

THEOREM CrashBetweenCheckAndCommitCannotCreateAnEffect ==
    CrashBetweenCheckAndCommit =>
      /\ phase' = phase
      /\ effectCount' = effectCount
      /\ evidenceState' = evidenceState
      /\ crashed'
BY SMT DEF CrashBetweenCheckAndCommit, operationVars

THEOREM CrashAfterEffectPreservesRecoveryIntent ==
    CrashAfterEffect =>
      /\ phase' = "recovering"
      /\ effectCount' = 1
      /\ effectDurable'
      /\ recoveryIntent'
      /\ crashed'
BY SMT DEF CrashAfterEffect, operationVars

THEOREM CrashBeforeEvidencePreservesRecoveryIntent ==
    CrashBeforeEvidencePublication =>
      /\ phase' = "recovering"
      /\ effectCount' = 1
      /\ evidenceState' \in {"pending", "lost"}
      /\ recoveryIntent'
      /\ crashed'
BY SMT DEF CrashBeforeEvidencePublication, operationVars

THEOREM CrashAfterCommitPreservesDurableOutcome ==
    CrashAfterCommit =>
      /\ phase' = "committed"
      /\ effectCount' = effectCount
      /\ effectDurable' = effectDurable
      /\ evidenceState' = evidenceState
      /\ crashed'
BY SMT DEF CrashAfterCommit, operationVars

THEOREM PartitionedDistributedCommitIsRejectedWithoutEffect ==
    RejectPartitionedCommit =>
      /\ Profile = "bounded-distributed"
      /\ phase' = "rejected"
      /\ effectCount' = effectCount
      /\ clientResponse' = "rejected"
      /\ lastFailure' = "partition"
BY SMT DEF RejectPartitionedCommit

THEOREM GovernedConfigurationUsesAcceptedProfileRelation ==
    (AcceptedProfileRelationSurfaceBound
      /\ ProfileStateAbstractionBound
      /\ GovernedConfigurationUpdate
      /\ ProfileBridgeUpdate) =>
      <<priorProfileState', profileState'>>
        \in IF Profile = "bounded-distributed"
              THEN ProfileReconfigurationSteps
              ELSE ProfilePostMediationSteps(Profile)["shared"]
BY SMT DEF AcceptedProfileRelationSurfaceBound,
           ProfileStateAbstractionBound, GovernedConfigurationUpdate,
           ProfileBridgeUpdate, ProfileStateFor, configVars, operationVars

THEOREM AdmissionUsesAcceptedProfileRelation ==
    (AcceptedProfileRelationSurfaceBound
      /\ ProfileStateAbstractionBound /\ Admit /\ ProfileBridgeUpdate) =>
      <<priorProfileState', profileState'>>
        \in ProfilePostMediationSteps(Profile)["shared"]
BY SMT DEF AcceptedProfileRelationSurfaceBound,
           ProfileStateAbstractionBound, Admit, ProfileBridgeUpdate,
           ProfileStateFor, DistributedExecutionReady,
           configVars, operationVars

THEOREM PreparationUsesAcceptedProfileRelation ==
    (AcceptedProfileRelationSurfaceBound
      /\ ProfileStateAbstractionBound
      /\ PrepareEffect /\ ProfileBridgeUpdate) =>
      <<priorProfileState', profileState'>>
        \in ProfilePostMediationSteps(Profile)["shared"]
BY SMT DEF AcceptedProfileRelationSurfaceBound,
           ProfileStateAbstractionBound, PrepareEffect, ProfileBridgeUpdate,
           ProfileStateFor, DistributedExecutionReady,
           configVars, operationVars

THEOREM AtomicCommitUsesAcceptedProfileRelation ==
    (AcceptedProfileRelationSurfaceBound
      /\ ProfileStateAbstractionBound
      /\ CommitAtomic /\ ProfileBridgeUpdate) =>
      <<priorProfileState', profileState'>>
        \in ProfileFormalCommitSteps(Profile)
BY SMT DEF AcceptedProfileRelationSurfaceBound,
           ProfileStateAbstractionBound, CommitAtomic, ProfileBridgeUpdate,
           ProfileStateFor, DistributedExecutionReady,
           configVars, operationVars

THEOREM RetryFailureUsesAcceptedProfileRelation ==
    (AcceptedProfileRelationSurfaceBound
      /\ ProfileStateAbstractionBound /\ FailBeforeEffect
      /\ ProfileBridgeUpdate) =>
      <<priorProfileState', profileState'>>
        \in IF Profile = "bounded-distributed"
              THEN ProfileRetrySteps
              ELSE ProfileIdentitySteps
BY SMT DEF AcceptedProfileRelationSurfaceBound,
           ProfileStateAbstractionBound, FailBeforeEffect,
           ProfileBridgeUpdate, ProfileStateFor,
           DistributedExecutionReady, ProfileIdentitySteps,
           configVars, operationVars

THEOREM EvidenceRecoveryUsesAcceptedProfileRelation ==
    (AcceptedProfileRelationSurfaceBound
      /\ ProfileStateAbstractionBound /\ RecoverEvidence
      /\ ProfileBridgeUpdate) =>
      <<priorProfileState', profileState'>>
        \in ProfileFormalCommitSteps(Profile)
BY SMT DEF AcceptedProfileRelationSurfaceBound,
           ProfileStateAbstractionBound, RecoverEvidence,
           ProfileBridgeUpdate, ProfileStateFor,
           DistributedExecutionReady, configVars, operationVars

THEOREM PartitionUsesAcceptedProfileRelation ==
    (AcceptedProfileRelationSurfaceBound
      /\ ProfileStateAbstractionBound /\ Partition /\ ProfileBridgeUpdate) =>
      <<priorProfileState', profileState'>> \in ProfilePartitionSteps
BY SMT DEF AcceptedProfileRelationSurfaceBound,
           ProfileStateAbstractionBound, Partition, ProfileBridgeUpdate,
           ProfileStateFor, configVars, operationVars

THEOREM PartitionRecoveryUsesAcceptedProfileRelation ==
    (AcceptedProfileRelationSurfaceBound
      /\ ProfileStateAbstractionBound /\ NoPartitionedCommit
      /\ HealPartition
      /\ ProfileBridgeUpdate) =>
      <<priorProfileState', profileState'>> \in ProfileRecoverySteps
BY SMT DEF AcceptedProfileRelationSurfaceBound,
           ProfileStateAbstractionBound, NoPartitionedCommit,
           HealPartition, ProfileBridgeUpdate, ProfileStateFor,
           configVars, operationVars

THEOREM DistributedAuditLossUsesAcceptedProfileRelation ==
    (Profile = "bounded-distributed"
      /\ configVersion = 2
      /\ AcceptedProfileRelationSurfaceBound
      /\ ProfileStateAbstractionBound /\ LoseAuditAfterCommit
      /\ ProfileBridgeUpdate) =>
      <<priorProfileState', profileState'>>
        \in ProfileAuditLossSteps(Profile)
BY SMT DEF AcceptedProfileRelationSurfaceBound,
           ProfileStateAbstractionBound, LoseAuditAfterCommit,
           ProfileBridgeUpdate, ProfileStateFor,
           DistributedExecutionReady, ProfileAuditLossSteps,
           configVars, operationVars

THEOREM NondistributedAuditLossUsesAcceptedProfileRelation ==
    (Profile # "bounded-distributed"
      /\ AcceptedProfileRelationSurfaceBound
      /\ ProfileStateAbstractionBound /\ LoseAuditAfterCommit
      /\ ProfileBridgeUpdate) =>
      <<priorProfileState', profileState'>>
        \in ProfileAuditLossSteps(Profile)
BY SMT DEF AcceptedProfileRelationSurfaceBound,
           ProfileStateAbstractionBound, LoseAuditAfterCommit,
           ProfileBridgeUpdate, ProfileStateFor,
           DistributedExecutionReady, ProfileAuditLossSteps,
           configVars, operationVars

=============================================================================
