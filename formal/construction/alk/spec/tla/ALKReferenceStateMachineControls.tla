--------------- MODULE ALKReferenceStateMachineControls ---------------
EXTENDS ALKReferenceStateMachine

CONSTANT ControlName

ControlNames ==
    {"excluded-path", "effect-without-admission", "commit-without-evidence",
     "commit-owner-mismatch",
     "duplicate-effect", "stale-epoch-commit", "recovery-intent-loss",
     "lost-response-replay", "owner-version-drift",
     "guarantee-version-drift", "tcb-version-drift",
     "stale-credential-admission", "partition-commit",
     "detached-recovery", "evidence-custody-loss",
     "success-without-evidence", "configuration-epoch-drift",
     "membership-drift", "credential-epoch-drift"}
      \cup {"reordered-request-effect", "owner-value-drift",
             "guarantee-value-drift", "tcb-value-drift",
              "tcb-dependency-shrink", "guarantee-overclaim",
              "conflicting-digest-alias", "reordered-request-not-older",
              "action-path-mismatch", "stale-replay-current-epoch",
              "profile-bridge-hidden-reconfiguration",
              "profile-bridge-partition-before-reconfiguration",
              "profile-bridge-commit-label-alias"}

ASSUME ControlName \in ControlNames

SetStatus(action, path, failure) ==
    /\ lastAction' = action
    /\ lastPath' = path
    /\ lastFailure' = failure

ExcludedPathMutation ==
    /\ phase = "idle"
    /\ SetStatus("admit", "debug", "none")
    /\ UNCHANGED <<configVars, operationVars, crashed, partitioned>>

EffectWithoutAdmissionMutation ==
    /\ phase = "idle"
    /\ effectCount' = 1
    /\ effectOwner' = "builder-primary"
    /\ SetStatus("apply-before-evidence", "external-service",
                 "partial-persistence")
    /\ UNCHANGED
         <<configVars, phase, operationId, requestDigest, presentedDigest,
           requestEpoch, requestOrder, presentedOrder, attempts,
           effectDurable, evidenceState, custodyState,
           recoveryIntent, clientResponse, crashed, partitioned>>

CommitWithoutEvidenceMutation ==
    /\ phase = "prepared"
    /\ attempts < MaxAttempts
    /\ phase' = "committed"
    /\ attempts' = attempts + 1
    /\ effectCount' = 1
    /\ effectOwner' = "builder-primary"
    /\ effectDurable' = TRUE
    /\ evidenceState' = "none"
    /\ custodyState' = "none"
    /\ recoveryIntent' = FALSE
    /\ SetStatus("commit", "external-service", "none")
    /\ UNCHANGED
         <<configVars, operationId, requestDigest, presentedDigest,
           requestEpoch, requestOrder, presentedOrder,
           clientResponse, crashed, partitioned>>

CommitOwnerMismatchMutation ==
    /\ Profile = "local-reference"
    /\ phase = "prepared"
    /\ ~crashed
    /\ ~partitioned
    /\ authorizationAvailable
    /\ credentialEpoch = epoch
    /\ requestEpoch = epoch
    /\ attempts < MaxAttempts
    /\ effectCount = 0
    /\ phase' = "committed"
    /\ attempts' = attempts + 1
    /\ effectCount' = 1
    /\ effectOwner' = "external-owner-primary"
    /\ effectDurable' = TRUE
    /\ evidenceState' = "durable"
    /\ custodyState' = "custodian"
    /\ recoveryIntent' = FALSE
    /\ clientResponse' = "success"
    /\ SetStatus("commit", "external-service", "none")
    /\ UNCHANGED
         <<configVars, operationId, requestDigest, presentedDigest,
           requestEpoch, requestOrder, presentedOrder,
           crashed, partitioned>>

DuplicateEffectMutation ==
    /\ phase = "committed"
    /\ effectCount = 1
    /\ effectCount' = 2
    /\ SetStatus("duplicate", "credential", "none")
    /\ UNCHANGED
         <<configVars, phase, operationId, requestDigest, presentedDigest,
           requestEpoch, requestOrder, presentedOrder, attempts,
           effectOwner, effectDurable, evidenceState, custodyState,
           recoveryIntent, clientResponse, crashed, partitioned>>

StaleEpochCommitMutation ==
    /\ phase = "prepared"
    /\ attempts < MaxAttempts
    /\ phase' = "committed"
    /\ requestEpoch' = 0
    /\ attempts' = attempts + 1
    /\ effectCount' = 1
    /\ effectOwner' = "builder-primary"
    /\ effectDurable' = TRUE
    /\ evidenceState' = "durable"
    /\ custodyState' = "custodian"
    /\ recoveryIntent' = FALSE
    /\ clientResponse' = "success"
    /\ SetStatus("commit", "external-service", "stale-epoch")
    /\ UNCHANGED
         <<configVars, operationId, requestDigest, presentedDigest,
           requestOrder, presentedOrder, crashed, partitioned>>

RecoveryIntentLossMutation ==
    /\ phase = "recovering"
    /\ recoveryIntent
    /\ recoveryIntent' = FALSE
    /\ SetStatus("crash-after-effect", "recovery", "after-effect")
    /\ UNCHANGED
         <<configVars, phase, operationId, requestDigest, presentedDigest,
           requestEpoch, requestOrder, presentedOrder, attempts,
           effectCount, effectOwner, effectDurable,
           evidenceState, custodyState,
           clientResponse, crashed, partitioned>>

LostResponseReplayMutation ==
    /\ phase = "committed"
    /\ clientResponse = "lost"
    /\ effectCount' = 2
    /\ clientResponse' = "success"
    /\ SetStatus("retry-response", "credential", "none")
    /\ UNCHANGED
         <<configVars, phase, operationId, requestDigest, presentedDigest,
           requestEpoch, requestOrder, presentedOrder, attempts,
           effectOwner, effectDurable, evidenceState, custodyState,
           recoveryIntent, crashed, partitioned>>

OwnerVersionDriftMutation ==
    /\ phase = "idle"
    /\ configVersion = 1
    /\ ownerRevision' = 2
    /\ SetStatus("configure", "administrative", "none")
    /\ UNCHANGED
         <<configVersion, guaranteeRevision, tcbRevision, epoch, membership,
           credentialEpoch, authorizationAvailable, configuredOwner,
           configuredGuarantees, configuredTCB, operationVars,
           crashed, partitioned>>

GuaranteeVersionDriftMutation ==
    /\ phase = "idle"
    /\ configVersion = 1
    /\ guaranteeRevision' = 2
    /\ SetStatus("configure", "administrative", "none")
    /\ UNCHANGED
         <<configVersion, ownerRevision, tcbRevision, epoch, membership,
           credentialEpoch, authorizationAvailable, configuredOwner,
           configuredGuarantees, configuredTCB, operationVars,
           crashed, partitioned>>

TCBVersionDriftMutation ==
    /\ phase = "idle"
    /\ configVersion = 1
    /\ tcbRevision' = 2
    /\ SetStatus("configure", "administrative", "none")
    /\ UNCHANGED
         <<configVersion, ownerRevision, guaranteeRevision, epoch, membership,
           credentialEpoch, authorizationAvailable, configuredOwner,
           configuredGuarantees, configuredTCB, operationVars,
           crashed, partitioned>>

StaleCredentialAdmissionMutation ==
    /\ phase = "idle"
    /\ phase' = "admitted"
    /\ operationId' = "operation-a"
    /\ requestDigest' = "digest-a"
    /\ presentedDigest' = "digest-a"
    /\ requestEpoch' = 0
    /\ requestOrder' = 1
    /\ presentedOrder' = 1
    /\ attempts' = 0
    /\ clientResponse' = "accepted"
    /\ SetStatus("admit", "credential", "stale-epoch")
    /\ UNCHANGED
         <<configVars, effectCount, effectOwner, effectDurable, evidenceState,
           custodyState, recoveryIntent, crashed, partitioned>>

PartitionCommitMutation ==
    /\ Profile = "bounded-distributed"
    /\ phase = "prepared"
    /\ partitioned
    /\ attempts < MaxAttempts
    /\ phase' = "committed"
    /\ attempts' = attempts + 1
    /\ effectCount' = 1
    /\ effectOwner' = configuredOwner
    /\ effectDurable' = TRUE
    /\ evidenceState' = "durable"
    /\ custodyState' = "custodian"
    /\ recoveryIntent' = FALSE
    /\ clientResponse' = "success"
    /\ SetStatus("commit", "external-service", "partition")
    /\ UNCHANGED
         <<configVars, operationId, requestDigest, presentedDigest,
           requestEpoch, requestOrder, presentedOrder,
           crashed, partitioned>>

DetachedRecoveryMutation ==
    /\ phase = "recovering"
    /\ phase' = "committed"
    /\ evidenceState' = "durable"
    /\ custodyState' = "custodian"
    /\ recoveryIntent' = FALSE
    /\ clientResponse' = "success"
    /\ SetStatus("recover", "external-service", "none")
    /\ UNCHANGED
         <<configVars, operationId, requestDigest, presentedDigest,
           requestEpoch, requestOrder, presentedOrder, attempts,
           effectCount, effectOwner, effectDurable,
           crashed, partitioned>>

EvidenceCustodyLossMutation ==
    /\ phase = "committed"
    /\ evidenceState = "durable"
    /\ phase' = "recovering"
    /\ evidenceState' = "lost"
    /\ custodyState' = "producer"
    /\ recoveryIntent' = TRUE
    /\ clientResponse' = "lost"
    /\ SetStatus("lose-audit", "recovery", "audit-loss")
    /\ UNCHANGED
         <<configVars, operationId, requestDigest, presentedDigest,
           requestEpoch, requestOrder, presentedOrder, attempts,
           effectCount, effectOwner, effectDurable, crashed, partitioned>>

SuccessWithoutEvidenceMutation ==
    /\ phase = "prepared"
    /\ clientResponse' = "success"
    /\ SetStatus("commit", "external-service", "none")
    /\ UNCHANGED
         <<configVars, phase, operationId, requestDigest, presentedDigest,
           requestEpoch, requestOrder, presentedOrder, attempts,
           effectCount, effectOwner, effectDurable,
           evidenceState, custodyState,
           recoveryIntent, crashed, partitioned>>

ConfigurationEpochDriftMutation ==
    /\ phase = "idle"
    /\ configVersion = 1
    /\ configVersion' = 2
    /\ ownerRevision' = 2
    /\ guaranteeRevision' = 2
    /\ tcbRevision' = 2
    /\ membership' = MembershipFor(Profile, 2)
    /\ configuredOwner' = ConfiguredOwnerFor(Profile, 2)
    /\ configuredGuarantees' =
         ConfiguredGuaranteesFor(Profile, AssuranceMode, 2)
    /\ configuredTCB' = ConfiguredTCBFor(Profile, 2)
    /\ SetStatus("configure", "administrative", "none")
    /\ UNCHANGED
         <<epoch, credentialEpoch, authorizationAvailable, operationVars,
           crashed, partitioned>>

MembershipDriftMutation ==
    /\ Profile = "bounded-distributed"
    /\ phase = "idle"
    /\ configVersion = 1
    /\ configVersion' = 2
    /\ ownerRevision' = 2
    /\ guaranteeRevision' = 2
    /\ tcbRevision' = 2
    /\ epoch' = 2
    /\ credentialEpoch' = 2
    /\ configuredOwner' = ConfiguredOwnerFor(Profile, 2)
    /\ configuredGuarantees' =
         ConfiguredGuaranteesFor(Profile, AssuranceMode, 2)
    /\ configuredTCB' = ConfiguredTCBFor(Profile, 2)
    /\ SetStatus("configure", "administrative", "none")
    /\ UNCHANGED
         <<membership, authorizationAvailable, operationVars,
           crashed, partitioned>>

CredentialEpochDriftMutation ==
    /\ phase = "idle"
    /\ credentialEpoch' = 2
    /\ SetStatus("configure", "administrative", "none")
    /\ UNCHANGED
         <<configVersion, ownerRevision, guaranteeRevision, tcbRevision,
           epoch, membership, authorizationAvailable, operationVars,
           configuredOwner, configuredGuarantees, configuredTCB,
           crashed, partitioned>>

ReorderedRequestEffectMutation ==
    /\ phase = "prepared"
    /\ effectCount' = 1
    /\ effectOwner' = "builder-primary"
    /\ presentedDigest' = requestDigest
    /\ presentedOrder' = 0
    /\ clientResponse' = "stale"
    /\ SetStatus("reject-reordered", "credential", "reordered")
    /\ UNCHANGED
         <<configVars, phase, operationId, requestDigest, requestEpoch,
           requestOrder, attempts, effectDurable, evidenceState, custodyState,
           recoveryIntent, crashed, partitioned>>

OwnerValueDriftMutation ==
    /\ phase = "idle"
    /\ Profile = "local-reference"
    /\ configuredOwner' = "external-owner-primary"
    /\ SetStatus("configure", "administrative", "none")
    /\ UNCHANGED
         <<configVersion, ownerRevision, guaranteeRevision, tcbRevision,
           epoch, membership, credentialEpoch, authorizationAvailable,
           configuredGuarantees, configuredTCB, operationVars,
           crashed, partitioned>>

GuaranteeValueDriftMutation ==
    /\ phase = "idle"
    /\ configuredGuarantees' = {}
    /\ SetStatus("configure", "administrative", "none")
    /\ UNCHANGED
         <<configVersion, ownerRevision, guaranteeRevision, tcbRevision,
           epoch, membership, credentialEpoch, authorizationAvailable,
           configuredOwner, configuredTCB, operationVars,
           crashed, partitioned>>

TCBValueDriftMutation ==
    /\ phase = "idle"
    /\ Profile = "local-reference"
    /\ configuredTCB' = configuredTCB \cup {"membership-store"}
    /\ SetStatus("configure", "administrative", "none")
    /\ UNCHANGED
         <<configVersion, ownerRevision, guaranteeRevision, tcbRevision,
           epoch, membership, credentialEpoch, authorizationAvailable,
           configuredOwner, configuredGuarantees, operationVars,
           crashed, partitioned>>

TCBDependencyShrinkMutation ==
    /\ phase = "idle"
    /\ configuredTCB' = configuredTCB \ {"kernel-code"}
    /\ SetStatus("configure", "administrative", "none")
    /\ UNCHANGED
         <<configVersion, ownerRevision, guaranteeRevision, tcbRevision,
           epoch, membership, credentialEpoch, authorizationAvailable,
           configuredOwner, configuredGuarantees, operationVars,
           crashed, partitioned>>

GuaranteeOverclaimMutation ==
    /\ phase = "idle"
    /\ configuredGuarantees' = configuredGuarantees \cup {"lost"}
    /\ SetStatus("configure", "administrative", "none")
    /\ UNCHANGED
         <<configVersion, ownerRevision, guaranteeRevision, tcbRevision,
           epoch, membership, credentialEpoch, authorizationAvailable,
           configuredOwner, configuredTCB, operationVars,
           crashed, partitioned>>

ConflictingDigestAliasMutation ==
    /\ phase = "committed"
    /\ presentedDigest' = requestDigest
    /\ presentedOrder' = requestOrder
    /\ clientResponse' = "conflict"
    /\ SetStatus("conflicting-duplicate", "credential", "none")
    /\ UNCHANGED
         <<configVars, phase, operationId, requestDigest, requestEpoch,
           requestOrder, attempts, effectCount, effectOwner, effectDurable,
           evidenceState, custodyState, recoveryIntent,
           crashed, partitioned>>

ReorderedRequestNotOlderMutation ==
    /\ phase = "prepared"
    /\ presentedDigest' = requestDigest
    /\ presentedOrder' = requestOrder
    /\ clientResponse' = "stale"
    /\ SetStatus("reject-reordered", "credential", "reordered")
    /\ UNCHANGED
         <<configVars, phase, operationId, requestDigest, requestEpoch,
           requestOrder, attempts, effectCount, effectOwner, effectDurable,
           evidenceState, custodyState, recoveryIntent,
           crashed, partitioned>>

ActionPathMismatchMutation ==
    /\ phase = "idle"
    /\ SetStatus("configure", "credential", "none")
    /\ UNCHANGED <<configVars, operationVars, crashed, partitioned>>

StaleReplayCurrentEpochMutation ==
    /\ phase = "idle"
    /\ operationId = "none"
    /\ configVersion = 2
    /\ ~crashed
    /\ presentedDigest' = "digest-a"
    /\ presentedOrder' = 0
    /\ clientResponse' = "stale"
    /\ SetStatus("stale-replay", "credential", "stale-epoch")
    /\ UNCHANGED
         <<configVars, phase, operationId, requestDigest, requestEpoch,
           requestOrder, attempts, effectCount, effectOwner, effectDurable,
           evidenceState, custodyState, recoveryIntent,
           crashed, partitioned>>

ProfileBridgeHiddenReconfigurationMutation ==
    /\ Profile = "bounded-distributed"
    /\ phase = "idle"
    /\ operationId = "none"
    /\ configVersion = 1
    /\ ~crashed
    /\ ~partitioned
    /\ configVersion' = 2
    /\ ownerRevision' = 2
    /\ guaranteeRevision' = 2
    /\ tcbRevision' = 2
    /\ epoch' = 2
    /\ membership' = MembershipFor(Profile, 2)
    /\ credentialEpoch' = 2
    /\ authorizationAvailable' = TRUE
    /\ configuredOwner' = ConfiguredOwnerFor(Profile, 2)
    /\ configuredGuarantees' =
         ConfiguredGuaranteesFor(Profile, AssuranceMode, 2)
    /\ configuredTCB' = ConfiguredTCBFor(Profile, 2)
    /\ phase' = "admitted"
    /\ operationId' = "operation-a"
    /\ requestDigest' = "digest-a"
    /\ presentedDigest' = "digest-a"
    /\ requestEpoch' = 2
    /\ requestOrder' = 1
    /\ presentedOrder' = 1
    /\ attempts' = 0
    /\ clientResponse' = "accepted"
    /\ SetStatus("admit", "credential", "none")
    /\ UNCHANGED
         <<effectCount, effectOwner, effectDurable, evidenceState,
           custodyState, recoveryIntent, crashed, partitioned>>

ProfileBridgePartitionBeforeReconfigurationMutation ==
    /\ Profile = "bounded-distributed"
    /\ phase = "idle"
    /\ configVersion = 1
    /\ ~partitioned
    /\ ~crashed
    /\ partitioned' = TRUE
    /\ SetStatus("partition", "external-service", "partition")
    /\ UNCHANGED <<configVars, operationVars, crashed>>

ProfileBridgeCommitLabelAliasMutation ==
    /\ Profile = "local-reference"
    /\ phase = "prepared"
    /\ ~crashed
    /\ ~partitioned
    /\ authorizationAvailable
    /\ credentialEpoch = epoch
    /\ requestEpoch = epoch
    /\ attempts < MaxAttempts
    /\ effectCount = 0
    /\ phase' = "committed"
    /\ attempts' = attempts + 1
    /\ effectCount' = 1
    /\ effectOwner' = configuredOwner
    /\ effectDurable' = TRUE
    /\ evidenceState' = "durable"
    /\ custodyState' = "custodian"
    /\ recoveryIntent' = FALSE
    /\ clientResponse' = "success"
    /\ SetStatus("prepare", "credential", "none")
    /\ UNCHANGED
         <<configVars, operationId, requestDigest, presentedDigest,
           requestEpoch, requestOrder, presentedOrder,
           crashed, partitioned>>

SelectedMutation ==
    CASE ControlName = "excluded-path" -> ExcludedPathMutation
      [] ControlName = "effect-without-admission" ->
           EffectWithoutAdmissionMutation
      [] ControlName = "commit-without-evidence" ->
           CommitWithoutEvidenceMutation
      [] ControlName = "commit-owner-mismatch" ->
           CommitOwnerMismatchMutation
      [] ControlName = "duplicate-effect" -> DuplicateEffectMutation
      [] ControlName = "stale-epoch-commit" -> StaleEpochCommitMutation
      [] ControlName = "recovery-intent-loss" -> RecoveryIntentLossMutation
      [] ControlName = "lost-response-replay" -> LostResponseReplayMutation
      [] ControlName = "owner-version-drift" -> OwnerVersionDriftMutation
      [] ControlName = "guarantee-version-drift" ->
           GuaranteeVersionDriftMutation
      [] ControlName = "tcb-version-drift" -> TCBVersionDriftMutation
      [] ControlName = "stale-credential-admission" ->
           StaleCredentialAdmissionMutation
      [] ControlName = "partition-commit" -> PartitionCommitMutation
      [] ControlName = "detached-recovery" -> DetachedRecoveryMutation
      [] ControlName = "evidence-custody-loss" ->
           EvidenceCustodyLossMutation
      [] ControlName = "success-without-evidence" ->
           SuccessWithoutEvidenceMutation
      [] ControlName = "configuration-epoch-drift" ->
           ConfigurationEpochDriftMutation
      [] ControlName = "membership-drift" -> MembershipDriftMutation
      [] ControlName = "credential-epoch-drift" ->
           CredentialEpochDriftMutation
      [] ControlName = "reordered-request-effect" ->
           ReorderedRequestEffectMutation
      [] ControlName = "owner-value-drift" -> OwnerValueDriftMutation
      [] ControlName = "guarantee-value-drift" -> GuaranteeValueDriftMutation
      [] ControlName = "tcb-value-drift" -> TCBValueDriftMutation
      [] ControlName = "tcb-dependency-shrink" -> TCBDependencyShrinkMutation
      [] ControlName = "guarantee-overclaim" -> GuaranteeOverclaimMutation
      [] ControlName = "conflicting-digest-alias" ->
           ConflictingDigestAliasMutation
      [] ControlName = "reordered-request-not-older" ->
           ReorderedRequestNotOlderMutation
      [] ControlName = "action-path-mismatch" -> ActionPathMismatchMutation
      [] ControlName = "stale-replay-current-epoch" ->
           StaleReplayCurrentEpochMutation
      [] ControlName = "profile-bridge-hidden-reconfiguration" ->
           ProfileBridgeHiddenReconfigurationMutation
      [] ControlName = "profile-bridge-partition-before-reconfiguration" ->
           ProfileBridgePartitionBeforeReconfigurationMutation
      [] ControlName = "profile-bridge-commit-label-alias" ->
           ProfileBridgeCommitLabelAliasMutation

ControlSpotChecks ==
    CASE ControlName = "excluded-path" ->
           /\ OwnerRevisionBound
           /\ EffectAdmissionCoupled
           /\ NoDuplicateEffect
      [] ControlName = "effect-without-admission" ->
           /\ PathUseClassified
           /\ NoDuplicateEffect
           /\ EvidenceCustodyCoupled
      [] ControlName = "commit-without-evidence" ->
           /\ EffectAdmissionCoupled
           /\ CurrentEpochAtCommit
           /\ NoDuplicateEffect
      [] ControlName = "commit-owner-mismatch" ->
           /\ CommitEvidenceCoupled
           /\ CurrentEpochAtCommit
           /\ OwnerConfigurationBound
      [] ControlName = "duplicate-effect" ->
           /\ EffectAdmissionCoupled
           /\ EvidenceCustodyCoupled
      [] ControlName = "stale-epoch-commit" ->
           /\ CommitEvidenceCoupled
           /\ NoPartitionedCommit
           /\ EvidenceCustodyCoupled
      [] ControlName = "recovery-intent-loss" ->
           /\ EffectAdmissionCoupled
           /\ EvidenceEffectCoupled
           /\ EvidenceCustodyCoupled
           /\ NoDuplicateEffect
      [] ControlName = "lost-response-replay" ->
           /\ EffectAdmissionCoupled
           /\ EvidenceCustodyCoupled
      [] ControlName = "owner-version-drift" ->
           /\ GuaranteeRevisionBound
           /\ TCBRevisionBound
           /\ ConfigurationEpochBound
      [] ControlName = "guarantee-version-drift" ->
           /\ OwnerRevisionBound
           /\ TCBRevisionBound
           /\ ConfigurationEpochBound
      [] ControlName = "tcb-version-drift" ->
           /\ OwnerRevisionBound
           /\ GuaranteeRevisionBound
           /\ ConfigurationEpochBound
      [] ControlName = "stale-credential-admission" ->
           /\ IdentityEpochBound
           /\ ConfigurationEpochBound
           /\ PathUseClassified
      [] ControlName = "partition-commit" ->
           /\ CommitEvidenceCoupled
           /\ CurrentEpochAtCommit
           /\ NoDuplicateEffect
      [] ControlName = "detached-recovery" ->
           /\ CommitEvidenceCoupled
           /\ EvidenceCustodyCoupled
           /\ NoDuplicateEffect
      [] ControlName = "evidence-custody-loss" ->
           /\ EffectAdmissionCoupled
           /\ EvidenceEffectCoupled
           /\ NoDuplicateEffect
      [] ControlName = "success-without-evidence" ->
           /\ EffectAdmissionCoupled
           /\ EvidenceCustodyCoupled
           /\ NoDuplicateEffect
      [] ControlName = "configuration-epoch-drift" ->
           /\ OwnerRevisionBound
           /\ GuaranteeRevisionBound
           /\ TCBRevisionBound
           /\ MembershipEpochBound
           /\ IdentityEpochBound
      [] ControlName = "membership-drift" ->
           /\ OwnerRevisionBound
           /\ GuaranteeRevisionBound
           /\ TCBRevisionBound
           /\ ConfigurationEpochBound
           /\ IdentityEpochBound
      [] ControlName = "credential-epoch-drift" ->
           /\ OwnerRevisionBound
           /\ GuaranteeRevisionBound
           /\ TCBRevisionBound
           /\ ConfigurationEpochBound
           /\ MembershipEpochBound
      [] ControlName = "reordered-request-effect" ->
           /\ PathUseClassified
           /\ NoDuplicateEffect
           /\ EvidenceCustodyCoupled
      [] ControlName = "owner-value-drift" ->
           /\ OwnerRevisionBound
           /\ GuaranteeConfigurationBound
           /\ TCBConfigurationBound
      [] ControlName = "guarantee-value-drift" ->
           /\ GuaranteeRevisionBound
           /\ GuaranteeWithinCeiling
           /\ OwnerConfigurationBound
      [] ControlName = "tcb-value-drift" ->
           /\ TCBRevisionBound
           /\ OwnerConfigurationBound
           /\ GuaranteeConfigurationBound
      [] ControlName = "tcb-dependency-shrink" ->
           /\ TCBRevisionBound
           /\ OwnerConfigurationBound
           /\ GuaranteeConfigurationBound
      [] ControlName = "guarantee-overclaim" ->
           /\ GuaranteeRevisionBound
           /\ OwnerConfigurationBound
           /\ TCBConfigurationBound
      [] ControlName = "conflicting-digest-alias" ->
           /\ NoDuplicateEffect
           /\ EvidenceCustodyCoupled
           /\ SameRequestDuplicateBound
      [] ControlName = "reordered-request-not-older" ->
           /\ NoDuplicateEffect
           /\ EvidenceCustodyCoupled
           /\ PathUseClassified
      [] ControlName = "action-path-mismatch" ->
           /\ PathInventoryComplete
           /\ PathUseClassified
           /\ OwnerRevisionBound
      [] ControlName = "stale-replay-current-epoch" ->
           /\ ConfigurationEpochBound
           /\ IdentityEpochBound
           /\ NoDuplicateEffect
      [] ControlName = "profile-bridge-hidden-reconfiguration" ->
           /\ ConfigurationEpochBound
           /\ MembershipEpochBound
           /\ FailSafeAdmissionHeld
      [] ControlName = "profile-bridge-partition-before-reconfiguration" ->
           /\ ConfigurationEpochBound
           /\ MembershipEpochBound
           /\ NoPartitionedCommit
      [] ControlName = "profile-bridge-commit-label-alias" ->
           /\ CommitEvidenceCoupled
           /\ EffectOwnerCoupled
           /\ CurrentEpochAtCommit

SemanticInvariantNames ==
    {"ProfileRelationInventoryComplete", "AcceptedProfileRelationSurfaceBound",
     "ProfileStateAbstractionBound",
     "ProfileVersionMembershipBound", "ProfileRelationBridgeBound",
     "ProfileObservationBridgeBound",
     "OwnerRevisionBound", "GuaranteeRevisionBound", "TCBRevisionBound",
     "ConfigurationEpochBound", "IdentityEpochBound", "MembershipEpochBound",
     "OwnerConfigurationBound", "GuaranteeConfigurationBound",
     "TCBConfigurationBound", "PathInventoryComplete",
     "ActionPathInventoryComplete", "ExcludedPathsAbsent",
     "PathUseClassified", "ActionPathBound", "OperationIdentityBound",
     "EffectAdmissionCoupled", "EffectOwnerCoupled",
     "CommitAdmissionCoupled",
     "CommitEvidenceCoupled", "EvidenceEffectCoupled",
     "EvidenceCustodyCoupled", "SuccessCoupled", "RetryReplayIdempotent",
     "SameRequestDuplicateBound", "ConflictingDigestSeparated",
     "StaleReplayBound", "RecoveryPathGoverned", "ReorderedRequestSafe",
     "NoDuplicateEffect", "CurrentEpochAtCommit", "FailSafeAdmissionHeld",
     "NoPartitionedCommit", "RecoveryIntentCoupled", "TCBClosed",
     "GuaranteeWithinCeiling", "ProfileContractBound"}

InvariantHolds(name) ==
    CASE name = "ProfileRelationInventoryComplete" ->
           ProfileRelationInventoryComplete
      [] name = "AcceptedProfileRelationSurfaceBound" ->
           AcceptedProfileRelationSurfaceBound
      [] name = "ProfileStateAbstractionBound" ->
           ProfileStateAbstractionBound
      [] name = "ProfileVersionMembershipBound" ->
           ProfileVersionMembershipBound
      [] name = "ProfileRelationBridgeBound" ->
           ProfileRelationBridgeBound
      [] name = "ProfileObservationBridgeBound" ->
           ProfileObservationBridgeBound
      [] name = "OwnerRevisionBound" -> OwnerRevisionBound
      [] name = "GuaranteeRevisionBound" -> GuaranteeRevisionBound
      [] name = "TCBRevisionBound" -> TCBRevisionBound
      [] name = "ConfigurationEpochBound" -> ConfigurationEpochBound
      [] name = "IdentityEpochBound" -> IdentityEpochBound
      [] name = "MembershipEpochBound" -> MembershipEpochBound
      [] name = "OwnerConfigurationBound" -> OwnerConfigurationBound
      [] name = "GuaranteeConfigurationBound" -> GuaranteeConfigurationBound
      [] name = "TCBConfigurationBound" -> TCBConfigurationBound
      [] name = "PathInventoryComplete" -> PathInventoryComplete
      [] name = "ActionPathInventoryComplete" -> ActionPathInventoryComplete
      [] name = "ExcludedPathsAbsent" -> ExcludedPathsAbsent
      [] name = "PathUseClassified" -> PathUseClassified
      [] name = "ActionPathBound" -> ActionPathBound
      [] name = "OperationIdentityBound" -> OperationIdentityBound
      [] name = "EffectAdmissionCoupled" -> EffectAdmissionCoupled
      [] name = "EffectOwnerCoupled" -> EffectOwnerCoupled
      [] name = "CommitAdmissionCoupled" -> CommitAdmissionCoupled
      [] name = "CommitEvidenceCoupled" -> CommitEvidenceCoupled
      [] name = "EvidenceEffectCoupled" -> EvidenceEffectCoupled
      [] name = "EvidenceCustodyCoupled" -> EvidenceCustodyCoupled
      [] name = "SuccessCoupled" -> SuccessCoupled
      [] name = "RetryReplayIdempotent" -> RetryReplayIdempotent
      [] name = "SameRequestDuplicateBound" -> SameRequestDuplicateBound
      [] name = "ConflictingDigestSeparated" -> ConflictingDigestSeparated
      [] name = "StaleReplayBound" -> StaleReplayBound
      [] name = "RecoveryPathGoverned" -> RecoveryPathGoverned
      [] name = "ReorderedRequestSafe" -> ReorderedRequestSafe
      [] name = "NoDuplicateEffect" -> NoDuplicateEffect
      [] name = "CurrentEpochAtCommit" -> CurrentEpochAtCommit
      [] name = "FailSafeAdmissionHeld" -> FailSafeAdmissionHeld
      [] name = "NoPartitionedCommit" -> NoPartitionedCommit
      [] name = "RecoveryIntentCoupled" -> RecoveryIntentCoupled
      [] name = "TCBClosed" -> TCBClosed
      [] name = "GuaranteeWithinCeiling" -> GuaranteeWithinCeiling
      [] name = "ProfileContractBound" -> ProfileContractBound

ControlTargetName(control) ==
    CASE control = "excluded-path" -> "PathUseClassified"
      [] control = "effect-without-admission" -> "EffectAdmissionCoupled"
      [] control = "commit-without-evidence" -> "CommitEvidenceCoupled"
      [] control = "commit-owner-mismatch" -> "EffectOwnerCoupled"
      [] control = "duplicate-effect" -> "NoDuplicateEffect"
      [] control = "stale-epoch-commit" -> "CurrentEpochAtCommit"
      [] control = "recovery-intent-loss" -> "RecoveryIntentCoupled"
      [] control = "lost-response-replay" -> "RetryReplayIdempotent"
      [] control = "owner-version-drift" -> "OwnerRevisionBound"
      [] control = "guarantee-version-drift" -> "GuaranteeRevisionBound"
      [] control = "tcb-version-drift" -> "TCBRevisionBound"
      [] control = "stale-credential-admission" -> "FailSafeAdmissionHeld"
      [] control = "partition-commit" -> "NoPartitionedCommit"
      [] control = "detached-recovery" -> "RecoveryPathGoverned"
      [] control = "evidence-custody-loss" -> "EvidenceCustodyCoupled"
      [] control = "success-without-evidence" -> "SuccessCoupled"
      [] control = "configuration-epoch-drift" -> "ConfigurationEpochBound"
      [] control = "membership-drift" -> "MembershipEpochBound"
      [] control = "credential-epoch-drift" -> "IdentityEpochBound"
      [] control = "reordered-request-effect" -> "ReorderedRequestSafe"
      [] control = "owner-value-drift" -> "OwnerConfigurationBound"
      [] control = "guarantee-value-drift" -> "GuaranteeConfigurationBound"
      [] control = "tcb-value-drift" -> "TCBConfigurationBound"
      [] control = "tcb-dependency-shrink" -> "TCBClosed"
      [] control = "guarantee-overclaim" -> "GuaranteeWithinCeiling"
      [] control = "conflicting-digest-alias" -> "ConflictingDigestSeparated"
      [] control = "reordered-request-not-older" -> "ReorderedRequestSafe"
      [] control = "action-path-mismatch" -> "ActionPathBound"
      [] control = "stale-replay-current-epoch" -> "StaleReplayBound"
      [] control = "profile-bridge-hidden-reconfiguration" ->
           "ProfileRelationBridgeBound"
      [] control = "profile-bridge-partition-before-reconfiguration" ->
           "ProfileRelationBridgeBound"
      [] control = "profile-bridge-commit-label-alias" ->
           "ProfileRelationBridgeBound"

ControlDependentFailures(control) ==
    CASE control = "excluded-path" -> {"ActionPathBound"}
      [] control = "stale-epoch-commit" ->
           {"OperationIdentityBound", "FailSafeAdmissionHeld"}
      [] control = "duplicate-effect" ->
           {"CommitEvidenceCoupled", "EvidenceEffectCoupled",
            "SuccessCoupled"}
      [] control = "lost-response-replay" ->
           {"CommitEvidenceCoupled", "EvidenceEffectCoupled",
            "SuccessCoupled", "NoDuplicateEffect"}
      [] control = "stale-credential-admission" ->
           {"OperationIdentityBound"}
      [] control = "detached-recovery" -> {"ActionPathBound"}
      [] control = "evidence-custody-loss" -> {"CommitEvidenceCoupled"}
      [] control = "reordered-request-effect" -> {"EffectAdmissionCoupled"}
      [] control = "owner-value-drift" -> {"ProfileContractBound"}
      [] control = "tcb-dependency-shrink" -> {"TCBConfigurationBound"}
      [] control = "guarantee-overclaim" -> {"GuaranteeConfigurationBound"}
      [] control = "membership-drift" ->
           {"ProfileVersionMembershipBound"}
      [] control = "partition-commit" ->
           {"ProfileRelationBridgeBound"}
      [] control = "success-without-evidence" ->
           {"ProfileRelationBridgeBound", "ProfileObservationBridgeBound"}
      [] control = "profile-bridge-partition-before-reconfiguration" ->
           {"ProfileVersionMembershipBound"}
      [] OTHER -> {}

ControlAllowedFailures(control) ==
    {ControlTargetName(control)} \cup ControlDependentFailures(control)

ControlAdjacentBoundary ==
    /\ ControlSpotChecks
    /\ \A name \in
          SemanticInvariantNames \ ControlAllowedFailures(ControlName) :
          InvariantHolds(name)

ControlPresentedEpochUpdate ==
    IF ControlName = "stale-replay-current-epoch"
      THEN presentedEpoch' = epoch
      ELSE IF ControlName = "profile-bridge-hidden-reconfiguration"
        THEN presentedEpoch' = requestEpoch'
      ELSE UNCHANGED presentedEpoch

ControlProfileBridgeUpdate ==
    /\ priorProfileState' = profileState
    /\ profileState' =
         ProfileStateFor(Profile, configVersion', partitioned', phase')

ControlNext ==
    \/ Next
    \/ /\ UNCHANGED progressState
       /\ SelectedMutation
       /\ ControlPresentedEpochUpdate
       /\ ControlProfileBridgeUpdate

ControlSpec == Init /\ [][ControlNext]_vars

=============================================================================
