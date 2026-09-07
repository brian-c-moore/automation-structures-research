--------------------- MODULE ALKReferenceStateMachine ---------------------
EXTENDS Naturals, FiniteSets

Certificate == INSTANCE ALKReferenceClaimAuthority

VARIABLES
    phase,
    configVersion, ownerRevision, guaranteeRevision, tcbRevision,
    epoch, membership, credentialEpoch, authorizationAvailable,
    configuredOwner, configuredGuarantees, configuredTCB,
    operationId, requestDigest, presentedDigest, requestEpoch, presentedEpoch,
    requestOrder, presentedOrder, attempts,
    effectCount, effectOwner, effectDurable,
    evidenceState, custodyState, recoveryIntent,
    clientResponse, crashed, partitioned,
    lastAction, lastPath, lastFailure,
    profileState, priorProfileState, progressState

ProfileWitness == INSTANCE ALKProfilesWitness
    WITH phase <- phase, progressState <- progressState

ProfileNames == ProfileWitness!ProfileNames
ProfileStates == ProfileWitness!ProfileStates
ProfilePostMediationSteps(profile) ==
    ProfileWitness!ProfilePostMediationSteps(profile)
ProfileFormalCommitSteps(profile) ==
    ProfileWitness!ProfileFormalCommitSteps(profile)
ProfileFormalObserve == ProfileWitness!ProfileFormalObserve
ProfileMembershipOf == ProfileWitness!ProfileMembershipOf
ProfileEpochOf == ProfileWitness!ProfileEpochOf
ProfileReconfigurationSteps == ProfileWitness!ProfileReconfigurationSteps
ProfileRetrySteps == ProfileWitness!ProfileRetrySteps
ProfilePartitionSteps == ProfileWitness!ProfilePartitionSteps
ProfileRecoverySteps == ProfileWitness!ProfileRecoverySteps
ExpectedProfileCommitOwner(profile) ==
    ProfileWitness!ExpectedProfileCommitOwner(profile)
DelegatedPrecommitCeiling == ProfileWitness!DelegatedPrecommitCeiling
DelegatedPostcommitCeiling == ProfileWitness!DelegatedPostcommitCeiling
DelegatedUnavailableCeiling == ProfileWitness!DelegatedUnavailableCeiling
GuaranteeKinds == ProfileWitness!GuaranteeKinds

CONSTANTS Profile, AssuranceMode, MaxAttempts

ASSUME /\ Profile \in ProfileNames
       /\ AssuranceMode \in
            {"at-commit", "precommit", "postcommit", "unavailable"}
       /\ MaxAttempts \in Nat \ {0}

ReferenceSpecVersion == "ALK-SPEC-1"

Phases ==
    {"idle", "admitted", "prepared", "recovering", "committed",
     "rejected"}
Responses ==
    {"none", "accepted", "pending", "success", "lost", "conflict",
     "stale", "rejected"}
EvidenceStates == {"none", "pending", "durable", "lost"}
CustodyStates == {"none", "producer", "custodian", "lost"}
OperationIds == {"none", "operation-a"}
RequestDigests == {"none", "digest-a"}
PresentedDigests == {"none", "digest-a", "digest-b"}
RequestOrders == 0..1
PathNames ==
    {"credential", "direct-database", "debug", "shared-memory",
     "administrative", "recovery", "external-service"}
PathClasses == {"mediated", "external", "excluded"}
FailureOutcomes ==
    {"none", "before-check", "between-check-and-commit", "after-effect",
     "before-evidence", "after-commit", "retry-exhaustion",
     "partial-persistence", "partition", "stale-epoch", "audit-loss",
     "external-owner", "assurance-loss", "reordered"}
ActionNames ==
    {"init", "configure", "admit", "reject-unavailable", "prepare",
     "commit", "fail-before-effect", "apply-before-evidence", "recover",
     "lose-audit", "duplicate", "conflicting-duplicate", "lose-response",
     "retry-response", "stale-replay", "stale-read", "crash-before-check",
     "reject-reordered",
     "crash-between-check-and-commit", "crash-after-effect",
     "crash-before-evidence", "crash-after-commit", "restart", "partition",
     "heal-partition", "reject-partition", "external-owner-unavailable"}

NodeIds == {"single-node", "node-a", "node-b", "node-c"}
Dependencies ==
    {"kernel-code", "identity-authority", "configuration-store",
     "effect-provider", "audit-store", "recovery-store", "scheduler",
     "external-owner-adapter", "membership-store",
     "claim-configuration-v1", "claim-configuration-v2"}

OwnerBindings ==
    {"builder-primary", "builder-rotated",
     "external-owner-primary", "external-owner-rotated",
     "cluster-owner-primary", "cluster-owner-rotated"}

OwnerBindingRole(binding) ==
    CASE binding \in {"builder-primary", "builder-rotated"} -> "builder"
      [] binding \in
           {"external-owner-primary", "external-owner-rotated"} ->
           "external-owner"
      [] OTHER -> "cluster-owner"

CommitOwner(profile) == ExpectedProfileCommitOwner(profile)

MembershipFor(profile, version) ==
    IF profile = "bounded-distributed"
      THEN IF version = 1
             THEN {"node-a", "node-b"}
             ELSE {"node-b", "node-c"}
      ELSE {"single-node"}

PathClass(path) ==
    CASE path \in {"credential", "administrative", "recovery"} ->
           "mediated"
      [] path = "external-service" -> "external"
      [] OTHER -> "excluded"

CredentialActions ==
    {"init", "admit", "reject-unavailable", "prepare", "duplicate",
     "conflicting-duplicate", "retry-response", "stale-replay",
     "stale-read", "reject-reordered", "reject-partition"}

AdministrativeActions == {"configure"}

RecoveryActions ==
    {"recover", "lose-audit", "crash-before-check",
     "crash-between-check-and-commit", "crash-after-effect",
     "crash-before-evidence", "crash-after-commit", "restart",
     "heal-partition"}

ExternalServiceActions ==
    {"commit", "fail-before-effect", "apply-before-evidence",
     "lose-response", "partition", "external-owner-unavailable"}

ExpectedActionPath(action) ==
    CASE action \in CredentialActions -> "credential"
      [] action \in AdministrativeActions -> "administrative"
      [] action \in RecoveryActions -> "recovery"
      [] action \in ExternalServiceActions -> "external-service"

PathTransitions(path) ==
    CASE path = "credential" ->
           {<<"idle", "idle">>,
            <<"idle", "admitted">>,
            <<"idle", "rejected">>,
            <<"admitted", "prepared">>,
            <<"prepared", "prepared">>,
            <<"prepared", "rejected">>,
            <<"committed", "committed">>}
      [] path = "administrative" -> {<<"idle", "idle">>}
      [] path = "recovery" ->
           {<<"idle", "idle">>,
            <<"admitted", "admitted">>,
            <<"prepared", "prepared">>,
            <<"recovering", "recovering">>,
            <<"recovering", "committed">>,
            <<"committed", "recovering">>,
            <<"committed", "committed">>}
      [] path = "external-service" ->
           {<<"idle", "idle">>,
            <<"admitted", "admitted">>,
            <<"prepared", "prepared">>,
            <<"prepared", "committed">>,
            <<"prepared", "recovering">>,
            <<"prepared", "rejected">>,
            <<"recovering", "recovering">>,
            <<"committed", "committed">>}
      [] OTHER -> {}

BaseRequiredTCB(profile) ==
    {"kernel-code", "identity-authority", "configuration-store",
     "effect-provider", "audit-store", "recovery-store"}
      \cup IF profile = "bounded-distributed"
             THEN {"membership-store", "scheduler"}
             ELSE {}
      \cup IF profile = "delegated"
             THEN {"external-owner-adapter"}
             ELSE {}

RequiredTCB(profile, version) ==
    BaseRequiredTCB(profile)
      \cup IF version = 1
             THEN {"claim-configuration-v1"}
             ELSE {"claim-configuration-v2"}

HealthyNormalBundle ==
    {"prevention", "detection", "recovery", "conditional"}

AssuranceCeiling(profile, mode) ==
    IF profile # "delegated" \/ mode = "at-commit"
      THEN HealthyNormalBundle
      ELSE IF mode = "precommit"
        THEN DelegatedPrecommitCeiling
        ELSE IF mode = "postcommit"
          THEN DelegatedPostcommitCeiling
          ELSE DelegatedUnavailableCeiling

AdvertisedGuarantees(profile, mode) ==
    IF profile # "delegated" \/ mode = "at-commit"
      THEN HealthyNormalBundle
      ELSE IF mode = "precommit"
        THEN {"prevention", "conditional"}
        ELSE IF mode = "postcommit"
          THEN {"detection", "recovery", "conditional"}
          ELSE {"conditional"}

ConfiguredOwnerFor(profile, version) ==
    CASE ExpectedProfileCommitOwner(profile) = "builder" ->
           IF version = 1 THEN "builder-primary" ELSE "builder-rotated"
      [] ExpectedProfileCommitOwner(profile) = "external-owner" ->
           IF version = 1
             THEN "external-owner-primary"
             ELSE "external-owner-rotated"
      [] OTHER ->
           IF version = 1
             THEN "cluster-owner-primary"
             ELSE "cluster-owner-rotated"

UpdatedGuarantees(profile, mode) ==
    LET current == AdvertisedGuarantees(profile, mode)
    IN IF "recovery" \in current
         THEN current \ {"recovery"}
         ELSE IF "prevention" \in current
           THEN current \ {"prevention"}
           ELSE {}

ConfiguredGuaranteesFor(profile, mode, version) ==
    IF version = 1
      THEN AdvertisedGuarantees(profile, mode)
      ELSE UpdatedGuarantees(profile, mode)

ConfiguredTCBFor(profile, version) == RequiredTCB(profile, version)

ProfileSharedBridgeActions == {"admit", "prepare"}
ProfileExternalBridgeActions == {"duplicate", "retry-response"}
ProfileSpecialBridgeActions ==
    {"init", "configure", "commit", "recover", "fail-before-effect",
     "partition", "heal-partition", "lose-audit"}
ReferenceExtensionStutterActions ==
    {"reject-unavailable", "apply-before-evidence",
     "conflicting-duplicate", "lose-response", "stale-replay",
     "stale-read", "reject-reordered", "crash-before-check",
     "crash-between-check-and-commit", "crash-after-effect",
     "crash-before-evidence", "crash-after-commit", "restart",
     "reject-partition", "external-owner-unavailable"}

ProfileIdentitySteps == {<<state, state>> : state \in ProfileStates}

ProfileStateFor(profile, version, isPartitioned, operationPhase) ==
    IF operationPhase = "committed"
      THEN "closed"
      ELSE IF isPartitioned
        THEN "failed"
        ELSE IF /\ profile = "bounded-distributed"
                /\ version = 2
          THEN "reconfigured"
          ELSE "open"

ProfileAuditLossSteps(profile) ==
    IF profile = "bounded-distributed"
      THEN {<<"closed", "reconfigured">>}
      ELSE {<<"closed", "open">>}

ProfileBridgeRelation(action, profile) ==
    CASE action = "init" -> {<<"open", "open">>}
      [] action = "configure" ->
           IF profile = "bounded-distributed"
             THEN ProfileReconfigurationSteps
             ELSE ProfilePostMediationSteps(profile)["shared"]
      [] action \in ProfileSharedBridgeActions ->
           ProfilePostMediationSteps(profile)["shared"]
      [] action \in ProfileExternalBridgeActions ->
           ProfilePostMediationSteps(profile)["external"]
      [] action \in {"commit", "recover"} ->
           ProfileFormalCommitSteps(profile)
      [] action = "fail-before-effect" ->
           IF profile = "bounded-distributed"
             THEN ProfileRetrySteps
             ELSE ProfileIdentitySteps
      [] action = "partition" -> ProfilePartitionSteps
      [] action = "heal-partition" -> ProfileRecoverySteps
      [] action = "lose-audit" -> ProfileAuditLossSteps(profile)
      [] action \in ReferenceExtensionStutterActions ->
           ProfileIdentitySteps
      [] OTHER -> {}

ProfileEpochToken(version) ==
    IF version = 1 THEN "epoch-0" ELSE "epoch-1"

DistributedExecutionReady ==
    Profile = "bounded-distributed" => configVersion = 2

configVars ==
    <<configVersion, ownerRevision, guaranteeRevision, tcbRevision,
      epoch, membership, credentialEpoch, authorizationAvailable,
      configuredOwner, configuredGuarantees, configuredTCB>>
operationVars ==
    <<phase, operationId, requestDigest, presentedDigest, requestEpoch,
      presentedEpoch,
      requestOrder, presentedOrder, attempts,
      effectCount, effectOwner, effectDurable,
      evidenceState, custodyState, recoveryIntent,
      clientResponse>>
statusVars ==
    <<crashed, partitioned, lastAction, lastPath, lastFailure,
      profileState, priorProfileState, progressState>>
vars == <<configVars, operationVars, statusVars>>

Init ==
    /\ progressState = "unused"
    /\ phase = "idle"
    /\ configVersion = 1
    /\ ownerRevision = 1
    /\ guaranteeRevision = 1
    /\ tcbRevision = 1
    /\ epoch = 1
    /\ membership = MembershipFor(Profile, 1)
    /\ credentialEpoch = 1
    /\ authorizationAvailable = (AssuranceMode # "unavailable")
    /\ configuredOwner = ConfiguredOwnerFor(Profile, 1)
    /\ configuredGuarantees =
         ConfiguredGuaranteesFor(Profile, AssuranceMode, 1)
    /\ configuredTCB = ConfiguredTCBFor(Profile, 1)
    /\ operationId = "none"
    /\ requestDigest = "none"
    /\ presentedDigest = "none"
    /\ requestEpoch = 0
    /\ presentedEpoch = 0
    /\ requestOrder = 0
    /\ presentedOrder = 0
    /\ attempts = 0
    /\ effectCount = 0
    /\ effectOwner = "none"
    /\ effectDurable = FALSE
    /\ evidenceState = "none"
    /\ custodyState = "none"
    /\ recoveryIntent = FALSE
    /\ clientResponse = "none"
    /\ crashed = FALSE
    /\ partitioned = FALSE
    /\ lastAction = "init"
    /\ lastPath = "credential"
    /\ lastFailure = "none"
    /\ profileState = "open"
    /\ priorProfileState = "open"

GovernedConfigurationUpdate ==
    /\ phase = "idle"
    /\ operationId = "none"
    /\ ~crashed
    /\ ~partitioned
    /\ configVersion = 1
    /\ configVersion' = 2
    /\ ownerRevision' = 2
    /\ guaranteeRevision' = 2
    /\ tcbRevision' = 2
    /\ epoch' = 2
    /\ membership' = MembershipFor(Profile, 2)
    /\ credentialEpoch' = 2
    /\ authorizationAvailable' = (AssuranceMode # "unavailable")
    /\ configuredOwner' = ConfiguredOwnerFor(Profile, 2)
    /\ configuredGuarantees' =
         ConfiguredGuaranteesFor(Profile, AssuranceMode, 2)
    /\ configuredTCB' = ConfiguredTCBFor(Profile, 2)
    /\ lastAction' = "configure"
    /\ lastPath' = "administrative"
    /\ lastFailure' = "none"
    /\ UNCHANGED <<operationVars, crashed, partitioned>>

Admit ==
    /\ phase = "idle"
    /\ operationId = "none"
    /\ ~crashed
    /\ ~partitioned
    /\ authorizationAvailable
    /\ AssuranceMode # "unavailable"
    /\ DistributedExecutionReady
    /\ credentialEpoch = epoch
    /\ phase' = "admitted"
    /\ operationId' = "operation-a"
    /\ requestDigest' = "digest-a"
    /\ presentedDigest' = "digest-a"
    /\ requestEpoch' = epoch
    /\ requestOrder' = 1
    /\ presentedOrder' = 1
    /\ attempts' = 0
    /\ clientResponse' = "accepted"
    /\ lastAction' = "admit"
    /\ lastPath' = "credential"
    /\ lastFailure' = "none"
    /\ UNCHANGED <<configVars, effectCount, effectOwner, effectDurable,
                    evidenceState, custodyState, recoveryIntent,
                    crashed, partitioned>>

RejectUnavailableAssurance ==
    /\ phase = "idle"
    /\ operationId = "none"
    /\ ~crashed
    /\ ~authorizationAvailable
    /\ phase' = "rejected"
    /\ operationId' = "operation-a"
    /\ requestDigest' = "digest-a"
    /\ presentedDigest' = "digest-a"
    /\ requestEpoch' = epoch
    /\ requestOrder' = 1
    /\ presentedOrder' = 1
    /\ attempts' = 0
    /\ clientResponse' = "rejected"
    /\ lastAction' = "reject-unavailable"
    /\ lastPath' = "credential"
    /\ lastFailure' = "assurance-loss"
    /\ UNCHANGED <<configVars, effectCount, effectOwner, effectDurable,
                    evidenceState, custodyState, recoveryIntent,
                    crashed, partitioned>>

PrepareEffect ==
    /\ phase = "admitted"
    /\ ~crashed
    /\ ~partitioned
    /\ DistributedExecutionReady
    /\ phase' = "prepared"
    /\ clientResponse' = "pending"
    /\ lastAction' = "prepare"
    /\ lastPath' = "credential"
    /\ lastFailure' = "none"
    /\ UNCHANGED <<configVars, operationId, requestDigest, presentedDigest,
                    requestEpoch, requestOrder, presentedOrder, attempts,
                    effectCount, effectOwner, effectDurable, evidenceState,
                    custodyState, recoveryIntent, crashed, partitioned>>

CommitAtomic ==
    /\ phase = "prepared"
    /\ ~crashed
    /\ ~partitioned
    /\ DistributedExecutionReady
    /\ authorizationAvailable
    /\ AssuranceMode # "unavailable"
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
    /\ lastAction' = "commit"
    /\ lastPath' = "external-service"
    /\ lastFailure' = "none"
    /\ UNCHANGED <<configVars, operationId, requestDigest, presentedDigest,
                    requestEpoch, requestOrder, presentedOrder,
                    crashed, partitioned>>

FailBeforeEffect ==
    /\ phase = "prepared"
    /\ ~crashed
    /\ ~partitioned
    /\ DistributedExecutionReady
    /\ attempts < MaxAttempts
    /\ attempts' = attempts + 1
    /\ phase' = IF attempts' = MaxAttempts THEN "rejected" ELSE "prepared"
    /\ clientResponse' =
         IF attempts' = MaxAttempts THEN "rejected" ELSE "pending"
    /\ lastFailure' =
         IF attempts' = MaxAttempts THEN "retry-exhaustion" ELSE "none"
    /\ lastAction' = "fail-before-effect"
    /\ lastPath' = "external-service"
    /\ UNCHANGED <<configVars, operationId, requestDigest, presentedDigest,
                    requestEpoch, requestOrder, presentedOrder,
                    effectCount, effectOwner, effectDurable,
                    evidenceState, custodyState,
                    recoveryIntent, crashed, partitioned>>

ApplyEffectBeforeEvidence ==
    /\ phase = "prepared"
    /\ ~crashed
    /\ ~partitioned
    /\ DistributedExecutionReady
    /\ authorizationAvailable
    /\ credentialEpoch = epoch
    /\ requestEpoch = epoch
    /\ attempts < MaxAttempts
    /\ effectCount = 0
    /\ phase' = "recovering"
    /\ attempts' = attempts + 1
    /\ effectCount' = 1
    /\ effectOwner' = configuredOwner
    /\ effectDurable' = TRUE
    /\ evidenceState' = "pending"
    /\ custodyState' = "producer"
    /\ recoveryIntent' = TRUE
    /\ clientResponse' = "lost"
    /\ lastAction' = "apply-before-evidence"
    /\ lastPath' = "external-service"
    /\ lastFailure' = "partial-persistence"
    /\ UNCHANGED <<configVars, operationId, requestDigest, presentedDigest,
                    requestEpoch, requestOrder, presentedOrder,
                    crashed, partitioned>>

RecoverEvidence ==
    /\ phase = "recovering"
    /\ ~crashed
    /\ ~partitioned
    /\ DistributedExecutionReady
    /\ effectCount = 1
    /\ effectDurable
    /\ evidenceState \in {"pending", "lost"}
    /\ recoveryIntent
    /\ requestEpoch = epoch
    /\ phase' = "committed"
    /\ evidenceState' = "durable"
    /\ custodyState' = "custodian"
    /\ recoveryIntent' = FALSE
    /\ clientResponse' = "success"
    /\ lastAction' = "recover"
    /\ lastPath' = "recovery"
    /\ lastFailure' = "none"
    /\ UNCHANGED <<configVars, operationId, requestDigest, presentedDigest,
                    requestEpoch, requestOrder, presentedOrder, attempts,
                    effectCount, effectOwner, effectDurable,
                    crashed, partitioned>>

LoseAuditAfterCommit ==
    /\ phase = "committed"
    /\ ~crashed
    /\ ~partitioned
    /\ DistributedExecutionReady
    /\ effectCount = 1
    /\ effectDurable
    /\ evidenceState = "durable"
    /\ phase' = "recovering"
    /\ evidenceState' = "lost"
    /\ custodyState' = "lost"
    /\ recoveryIntent' = TRUE
    /\ clientResponse' = "lost"
    /\ lastAction' = "lose-audit"
    /\ lastPath' = "recovery"
    /\ lastFailure' = "audit-loss"
    /\ UNCHANGED <<configVars, operationId, requestDigest, presentedDigest,
                    requestEpoch, requestOrder, presentedOrder, attempts,
                    effectCount, effectOwner, effectDurable,
                    crashed, partitioned>>

DuplicateSameRequest ==
    /\ phase = "committed"
    /\ ~crashed
    /\ operationId = "operation-a"
    /\ requestDigest = "digest-a"
    /\ presentedDigest' = requestDigest
    /\ presentedOrder' = requestOrder
    /\ clientResponse' = "success"
    /\ lastAction' = "duplicate"
    /\ lastPath' = "credential"
    /\ lastFailure' = "none"
    /\ UNCHANGED <<configVars, phase, operationId, requestDigest,
                    requestEpoch, requestOrder, attempts,
                    effectCount, effectOwner, effectDurable,
                    evidenceState, custodyState, recoveryIntent,
                    crashed, partitioned>>

ConflictingDuplicate ==
    /\ phase = "committed"
    /\ ~crashed
    /\ operationId = "operation-a"
    /\ requestDigest = "digest-a"
    /\ presentedDigest' = "digest-b"
    /\ presentedOrder' = requestOrder
    /\ clientResponse' = "conflict"
    /\ lastAction' = "conflicting-duplicate"
    /\ lastPath' = "credential"
    /\ lastFailure' = "none"
    /\ UNCHANGED <<configVars, phase, operationId, requestDigest,
                    requestEpoch, requestOrder, attempts,
                    effectCount, effectOwner, effectDurable,
                    evidenceState, custodyState, recoveryIntent,
                    crashed, partitioned>>

LoseResponse ==
    /\ phase = "committed"
    /\ ~crashed
    /\ clientResponse' = "lost"
    /\ lastAction' = "lose-response"
    /\ lastPath' = "external-service"
    /\ lastFailure' = "none"
    /\ UNCHANGED <<configVars, phase, operationId, requestDigest, presentedDigest,
                    requestEpoch, requestOrder, presentedOrder, attempts,
                    effectCount, effectOwner, effectDurable,
                    evidenceState, custodyState, recoveryIntent,
                    crashed, partitioned>>

RetryLostResponse ==
    /\ phase = "committed"
    /\ ~crashed
    /\ clientResponse = "lost"
    /\ presentedDigest' = requestDigest
    /\ presentedOrder' = requestOrder
    /\ clientResponse' = "success"
    /\ lastAction' = "retry-response"
    /\ lastPath' = "credential"
    /\ lastFailure' = "none"
    /\ UNCHANGED <<configVars, phase, operationId, requestDigest,
                    requestEpoch, requestOrder, attempts,
                    effectCount, effectOwner, effectDurable,
                    evidenceState, custodyState, recoveryIntent,
                    crashed, partitioned>>

ReplayStaleRequest ==
    /\ phase = "idle"
    /\ operationId = "none"
    /\ configVersion = 2
    /\ ~crashed
    /\ presentedDigest' = "digest-a"
    /\ presentedOrder' = 0
    /\ clientResponse' = "stale"
    /\ lastAction' = "stale-replay"
    /\ lastPath' = "credential"
    /\ lastFailure' = "stale-epoch"
    /\ UNCHANGED <<configVars, phase, operationId, requestDigest,
                    requestEpoch, requestOrder, attempts,
                    effectCount, effectOwner, effectDurable,
                    evidenceState, custodyState, recoveryIntent,
                    crashed, partitioned>>

ReadStaleState ==
    /\ phase = "idle"
    /\ configVersion = 2
    /\ ~crashed
    /\ clientResponse' = "stale"
    /\ lastAction' = "stale-read"
    /\ lastPath' = "credential"
    /\ lastFailure' = "stale-epoch"
    /\ UNCHANGED <<configVars, phase, operationId, requestDigest, presentedDigest,
                    requestEpoch, requestOrder, presentedOrder, attempts,
                    effectCount, effectOwner, effectDurable,
                    evidenceState, custodyState, recoveryIntent,
                    crashed, partitioned>>

RejectReorderedRequest ==
    /\ phase = "prepared"
    /\ ~crashed
    /\ requestDigest = "digest-a"
    /\ requestEpoch = epoch
    /\ requestOrder = 1
    /\ presentedDigest' = requestDigest
    /\ presentedOrder' = 0
    /\ clientResponse' = "stale"
    /\ lastAction' = "reject-reordered"
    /\ lastPath' = "credential"
    /\ lastFailure' = "reordered"
    /\ UNCHANGED <<configVars, phase, operationId, requestDigest,
                    requestEpoch, requestOrder, attempts,
                    effectCount, effectOwner, effectDurable,
                    evidenceState, custodyState, recoveryIntent,
                    crashed, partitioned>>

CrashBeforeCheck ==
    /\ phase = "idle"
    /\ ~crashed
    /\ crashed' = TRUE
    /\ lastAction' = "crash-before-check"
    /\ lastPath' = "recovery"
    /\ lastFailure' = "before-check"
    /\ UNCHANGED <<configVars, operationVars, partitioned>>

CrashBetweenCheckAndCommit ==
    /\ phase \in {"admitted", "prepared"}
    /\ ~crashed
    /\ crashed' = TRUE
    /\ lastAction' = "crash-between-check-and-commit"
    /\ lastPath' = "recovery"
    /\ lastFailure' = "between-check-and-commit"
    /\ UNCHANGED <<configVars, operationVars, partitioned>>

CrashAfterEffect ==
    /\ phase = "recovering"
    /\ effectCount = 1
    /\ effectDurable
    /\ evidenceState \in {"pending", "lost"}
    /\ recoveryIntent
    /\ ~crashed
    /\ crashed' = TRUE
    /\ lastAction' = "crash-after-effect"
    /\ lastPath' = "recovery"
    /\ lastFailure' = "after-effect"
    /\ UNCHANGED <<configVars, operationVars, partitioned>>

CrashBeforeEvidencePublication ==
    /\ phase = "recovering"
    /\ effectCount = 1
    /\ effectDurable
    /\ evidenceState \in {"pending", "lost"}
    /\ recoveryIntent
    /\ ~crashed
    /\ crashed' = TRUE
    /\ lastAction' = "crash-before-evidence"
    /\ lastPath' = "recovery"
    /\ lastFailure' = "before-evidence"
    /\ UNCHANGED <<configVars, operationVars, partitioned>>

CrashAfterCommit ==
    /\ phase = "committed"
    /\ ~crashed
    /\ crashed' = TRUE
    /\ lastAction' = "crash-after-commit"
    /\ lastPath' = "recovery"
    /\ lastFailure' = "after-commit"
    /\ UNCHANGED <<configVars, operationVars, partitioned>>

Restart ==
    /\ crashed
    /\ crashed' = FALSE
    /\ lastAction' = "restart"
    /\ lastPath' = "recovery"
    /\ UNCHANGED <<configVars, operationVars, partitioned, lastFailure>>

Partition ==
    /\ Profile = "bounded-distributed"
    /\ configVersion = 2
    /\ ~partitioned
    /\ ~crashed
    /\ phase \in {"idle", "admitted", "prepared", "recovering"}
    /\ partitioned' = TRUE
    /\ lastAction' = "partition"
    /\ lastPath' = "external-service"
    /\ lastFailure' = "partition"
    /\ UNCHANGED <<configVars, operationVars, crashed>>

HealPartition ==
    /\ Profile = "bounded-distributed"
    /\ configVersion = 2
    /\ partitioned
    /\ ~crashed
    /\ partitioned' = FALSE
    /\ lastAction' = "heal-partition"
    /\ lastPath' = "recovery"
    /\ UNCHANGED <<configVars, operationVars, crashed, lastFailure>>

RejectPartitionedCommit ==
    /\ Profile = "bounded-distributed"
    /\ phase = "prepared"
    /\ partitioned
    /\ ~crashed
    /\ phase' = "rejected"
    /\ clientResponse' = "rejected"
    /\ lastAction' = "reject-partition"
    /\ lastPath' = "credential"
    /\ lastFailure' = "partition"
    /\ UNCHANGED <<configVars, operationId, requestDigest, presentedDigest,
                    requestEpoch, requestOrder, presentedOrder, attempts,
                    effectCount, effectOwner, effectDurable, evidenceState,
                    custodyState, recoveryIntent, crashed, partitioned>>

ExternalOwnerUnavailable ==
    /\ Profile = "delegated"
    /\ phase = "prepared"
    /\ ~crashed
    /\ phase' = "rejected"
    /\ clientResponse' = "rejected"
    /\ lastAction' = "external-owner-unavailable"
    /\ lastPath' = "external-service"
    /\ lastFailure' = "external-owner"
    /\ UNCHANGED <<configVars, operationId, requestDigest, presentedDigest,
                    requestEpoch, requestOrder, presentedOrder, attempts,
                    effectCount, effectOwner, effectDurable, evidenceState,
                    custodyState, recoveryIntent, crashed, partitioned>>

PresentedEpochUpdate ==
    presentedEpoch' =
      CASE lastAction' \in
             {"admit", "reject-unavailable", "duplicate",
              "conflicting-duplicate", "retry-response",
              "reject-reordered"} -> requestEpoch'
        [] lastAction' = "stale-replay" -> 1
        [] OTHER -> presentedEpoch

ProfileBridgeUpdate ==
    /\ priorProfileState' = profileState
    /\ profileState' =
         ProfileStateFor(Profile, configVersion', partitioned', phase')

Next ==
    /\ UNCHANGED progressState
    /\ \/ GovernedConfigurationUpdate
       \/ Admit
       \/ RejectUnavailableAssurance
       \/ PrepareEffect
       \/ CommitAtomic
       \/ FailBeforeEffect
       \/ ApplyEffectBeforeEvidence
       \/ RecoverEvidence
       \/ LoseAuditAfterCommit
       \/ DuplicateSameRequest
       \/ ConflictingDuplicate
       \/ LoseResponse
       \/ RetryLostResponse
       \/ ReplayStaleRequest
       \/ ReadStaleState
       \/ RejectReorderedRequest
       \/ CrashBeforeCheck
       \/ CrashBetweenCheckAndCommit
       \/ CrashAfterEffect
       \/ CrashBeforeEvidencePublication
       \/ CrashAfterCommit
       \/ Restart
       \/ Partition
       \/ HealPartition
       \/ RejectPartitionedCommit
       \/ ExternalOwnerUnavailable
    /\ PresentedEpochUpdate
    /\ ProfileBridgeUpdate
    /\ <<phase, phase'>> \in PathTransitions(lastPath')

\* The original transition relation remains the conformance/vector authority.
\* The certificate gate admits exactly its classified actions under the
\* named closed-model protocol. It does not govern physical external faults.
ReferenceTransitionGate(action, actor, decision) ==
    /\ Next
    /\ lastAction' = action
    /\ Certificate!ReferenceAuthorization(Profile, configVersion, action, actor, decision)

CertifiedNext ==
    /\ Next
    /\ Certificate!ReferenceAuthorization(Profile, configVersion, lastAction',
           Certificate!ReferenceProtocol(Profile, configVersion),
           Certificate!ReferenceMembers)

Spec == Init /\ [][CertifiedNext]_vars

TypeInvariant ==
    /\ progressState = "unused"
    /\ phase \in Phases
    /\ configVersion \in 1..2
    /\ ownerRevision \in 1..2
    /\ guaranteeRevision \in 1..2
    /\ tcbRevision \in 1..2
    /\ epoch \in 1..2
    /\ membership \in SUBSET NodeIds
    /\ credentialEpoch \in 1..2
    /\ authorizationAvailable \in BOOLEAN
    /\ configuredOwner \in OwnerBindings
    /\ configuredGuarantees \in SUBSET GuaranteeKinds
    /\ configuredTCB \in SUBSET Dependencies
    /\ operationId \in OperationIds
    /\ requestDigest \in RequestDigests
    /\ presentedDigest \in PresentedDigests
    /\ requestEpoch \in 0..2
    /\ presentedEpoch \in 0..2
    /\ requestOrder \in RequestOrders
    /\ presentedOrder \in RequestOrders
    /\ attempts \in 0..MaxAttempts
    /\ effectCount \in 0..2
    /\ effectOwner \in OwnerBindings \cup {"none"}
    /\ effectDurable \in BOOLEAN
    /\ evidenceState \in EvidenceStates
    /\ custodyState \in CustodyStates
    /\ recoveryIntent \in BOOLEAN
    /\ clientResponse \in Responses
    /\ crashed \in BOOLEAN
    /\ partitioned \in BOOLEAN
    /\ lastAction \in ActionNames
    /\ lastPath \in PathNames
    /\ lastFailure \in FailureOutcomes
    /\ profileState \in ProfileStates
    /\ priorProfileState \in ProfileStates

ProfileRelationInventoryComplete ==
    /\ ProfileSharedBridgeActions \cup ProfileExternalBridgeActions
         \cup ProfileSpecialBridgeActions
         \cup ReferenceExtensionStutterActions = ActionNames
    /\ ProfileSharedBridgeActions \cap ProfileExternalBridgeActions = {}
    /\ ProfileSharedBridgeActions \cap ProfileSpecialBridgeActions = {}
    /\ ProfileSharedBridgeActions \cap ReferenceExtensionStutterActions = {}
    /\ ProfileExternalBridgeActions \cap ProfileSpecialBridgeActions = {}
    /\ ProfileExternalBridgeActions \cap ReferenceExtensionStutterActions = {}
    /\ ProfileSpecialBridgeActions \cap ReferenceExtensionStutterActions = {}

AcceptedProfileRelationSurfaceBound ==
    /\ ProfileStates = {"open", "reconfigured", "closed", "failed"}
    /\ ProfileReconfigurationSteps = {<<"open", "reconfigured">>}
    /\ ProfileRetrySteps = {<<"reconfigured", "reconfigured">>}
    /\ ProfilePartitionSteps = {<<"reconfigured", "failed">>}
    /\ ProfileRecoverySteps = {<<"failed", "reconfigured">>}
    /\ ProfilePostMediationSteps(Profile)["shared"] =
         IF Profile = "bounded-distributed"
           THEN {<<"reconfigured", "reconfigured">>}
           ELSE {<<"open", "open">>}
    /\ ProfilePostMediationSteps(Profile)["external"] =
         {<<"closed", "closed">>}
    /\ ProfileFormalCommitSteps(Profile) =
         IF Profile = "bounded-distributed"
           THEN {<<"reconfigured", "closed">>}
           ELSE {<<"open", "closed">>}

ProfileStateAbstractionBound ==
    profileState =
      ProfileStateFor(Profile, configVersion, partitioned, phase)

ProfileVersionMembershipBound ==
    Profile # "bounded-distributed" \/
      /\ membership = ProfileMembershipOf[profileState]
      /\ ProfileEpochOf[profileState] = ProfileEpochToken(epoch)

ProfileRelationBridgeBound ==
    <<priorProfileState, profileState>>
      \in ProfileBridgeRelation(lastAction, Profile)

ProfileObservationBridgeBound ==
    /\ (phase = "committed" <=> profileState = "closed")
    /\ (clientResponse = "success" =>
          ProfileFormalObserve[profileState] = "closed-view")

OwnerRevisionBound == ownerRevision = configVersion
GuaranteeRevisionBound == guaranteeRevision = configVersion
TCBRevisionBound == tcbRevision = configVersion
ConfigurationEpochBound == epoch = configVersion
IdentityEpochBound == credentialEpoch = epoch
MembershipEpochBound == membership = MembershipFor(Profile, configVersion)
OwnerConfigurationBound ==
    configuredOwner = ConfiguredOwnerFor(Profile, configVersion)
GuaranteeConfigurationBound ==
    configuredGuarantees =
      ConfiguredGuaranteesFor(Profile, AssuranceMode, configVersion)
TCBConfigurationBound == configuredTCB = ConfiguredTCBFor(Profile, configVersion)

PathInventoryComplete ==
    /\ DOMAIN [path \in PathNames |-> PathClass(path)] = PathNames
    /\ \A path \in PathNames : PathClass(path) \in PathClasses
    /\ \A path \in {"direct-database", "debug", "shared-memory"} :
          PathClass(path) = "excluded"

ActionPathInventoryComplete ==
    /\ CredentialActions \cup AdministrativeActions \cup RecoveryActions
         \cup ExternalServiceActions = ActionNames
    /\ CredentialActions \cap AdministrativeActions = {}
    /\ CredentialActions \cap RecoveryActions = {}
    /\ CredentialActions \cap ExternalServiceActions = {}
    /\ AdministrativeActions \cap RecoveryActions = {}
    /\ AdministrativeActions \cap ExternalServiceActions = {}
    /\ RecoveryActions \cap ExternalServiceActions = {}

ExcludedPathsAbsent ==
    \A path \in PathNames :
        PathClass(path) = "excluded" => PathTransitions(path) = {}

PathUseClassified == PathClass(lastPath) # "excluded"

ActionPathBound == lastPath = ExpectedActionPath(lastAction)

OperationIdentityBound ==
    phase # "idle" =>
      /\ operationId = "operation-a"
      /\ requestDigest = "digest-a"
      /\ requestEpoch \in 1..2
      /\ requestOrder = 1

EffectAdmissionCoupled ==
    effectCount > 0 =>
      /\ phase \in {"recovering", "committed"}
      /\ operationId = "operation-a"
      /\ requestDigest = "digest-a"

EffectOwnerCoupled ==
    effectCount > 0 =>
      /\ effectOwner = configuredOwner
      /\ OwnerBindingRole(effectOwner) = CommitOwner(Profile)

CommitAdmissionCoupled ==
    phase = "committed" =>
      /\ operationId = "operation-a"
      /\ requestDigest = "digest-a"
      /\ authorizationAvailable

CommitEvidenceCoupled ==
    phase = "committed" =>
      /\ effectCount = 1
      /\ effectDurable
      /\ evidenceState = "durable"
      /\ custodyState = "custodian"
      /\ ~recoveryIntent

EvidenceEffectCoupled ==
    evidenceState \in {"pending", "durable", "lost"} => effectCount = 1

EvidenceCustodyCoupled ==
    /\ (evidenceState = "none" => custodyState = "none")
    /\ (evidenceState = "pending" => custodyState = "producer")
    /\ (evidenceState = "durable" => custodyState = "custodian")
    /\ (evidenceState = "lost" => custodyState = "lost")

SuccessCoupled ==
    clientResponse = "success" =>
      /\ phase = "committed"
      /\ effectCount = 1
      /\ evidenceState = "durable"

RetryReplayIdempotent ==
    lastAction = "retry-response" =>
      /\ effectCount = 1
      /\ presentedDigest = requestDigest
      /\ presentedEpoch = requestEpoch
      /\ presentedOrder = requestOrder

SameRequestDuplicateBound ==
    lastAction = "duplicate" =>
      /\ presentedDigest = requestDigest
      /\ presentedEpoch = requestEpoch
      /\ presentedOrder = requestOrder

ConflictingDigestSeparated ==
    lastAction = "conflicting-duplicate" =>
      /\ presentedDigest # requestDigest
      /\ presentedEpoch = requestEpoch
      /\ presentedOrder = requestOrder

StaleReplayBound ==
    lastAction = "stale-replay" =>
      /\ phase = "idle"
      /\ configVersion = 2
      /\ presentedDigest = "digest-a"
      /\ presentedEpoch = 1
      /\ presentedEpoch < epoch
      /\ effectCount = 0
      /\ clientResponse = "stale"

RecoveryPathGoverned ==
    lastAction = "recover" => lastPath = "recovery"

ReorderedRequestSafe ==
    lastAction = "reject-reordered" =>
      /\ phase = "prepared"
      /\ effectCount = 0
      /\ evidenceState = "none"
      /\ clientResponse = "stale"
      /\ presentedDigest = requestDigest
      /\ presentedEpoch = requestEpoch
      /\ presentedOrder < requestOrder

NoDuplicateEffect == effectCount <= 1

CurrentEpochAtCommit ==
    phase = "committed" => requestEpoch = epoch

FailSafeAdmissionHeld ==
    phase \in {"admitted", "prepared", "recovering", "committed"} =>
      /\ authorizationAvailable
      /\ credentialEpoch = epoch
      /\ requestEpoch = epoch

NoPartitionedCommit == phase = "committed" => ~partitioned

RecoveryIntentCoupled ==
    phase = "recovering" =>
      /\ effectCount = 1
      /\ effectDurable
      /\ evidenceState \in {"pending", "lost"}
      /\ recoveryIntent

TCBClosed == RequiredTCB(Profile, configVersion) \subseteq configuredTCB

\* Compatibility field: configuredGuarantees contains the historical ceiling
\* labels used by the conformance vectors. Authoritative claim results below
\* carry complete frames and keep qualifiers/outcomes in separate fields.
LegacyGuaranteeWithinCeiling ==
    configuredGuarantees
      \subseteq AssuranceCeiling(Profile, AssuranceMode)

ReferenceCertificateKey ==
    [version |-> Certificate!ClaimCertificateVersion,
     profile |-> Profile, assuranceMode |-> AssuranceMode, revision |-> configVersion]

ReferencePredicateValues ==
    [claim \in Certificate!ReferenceClaimIds |->
        CASE claim = "reference-effect-count" -> NoDuplicateEffect
          [] claim = "reference-success-evidence" -> SuccessCoupled /\ CommitEvidenceCoupled
          [] OTHER -> EffectOwnerCoupled]

GuaranteeWithinCeiling == LegacyGuaranteeWithinCeiling

ProfileContractBound ==
    /\ CommitOwner(Profile) = OwnerBindingRole(configuredOwner)
    /\ IF Profile = "delegated"
         THEN AssuranceMode \in
              {"at-commit", "precommit", "postcommit", "unavailable"}
         ELSE AssuranceMode = "at-commit"

SpecInvariant ==
    /\ TypeInvariant
    /\ ProfileRelationInventoryComplete
    /\ AcceptedProfileRelationSurfaceBound
    /\ ProfileStateAbstractionBound
    /\ ProfileVersionMembershipBound
    /\ ProfileRelationBridgeBound
    /\ ProfileObservationBridgeBound
    /\ OwnerRevisionBound
    /\ GuaranteeRevisionBound
    /\ TCBRevisionBound
    /\ ConfigurationEpochBound
    /\ IdentityEpochBound
    /\ MembershipEpochBound
    /\ OwnerConfigurationBound
    /\ GuaranteeConfigurationBound
    /\ TCBConfigurationBound
    /\ PathInventoryComplete
    /\ ActionPathInventoryComplete
    /\ ExcludedPathsAbsent
    /\ PathUseClassified
    /\ ActionPathBound
    /\ OperationIdentityBound
    /\ EffectAdmissionCoupled
    /\ EffectOwnerCoupled
    /\ CommitAdmissionCoupled
    /\ CommitEvidenceCoupled
    /\ EvidenceEffectCoupled
    /\ EvidenceCustodyCoupled
    /\ SuccessCoupled
    /\ RetryReplayIdempotent
    /\ SameRequestDuplicateBound
    /\ ConflictingDigestSeparated
    /\ StaleReplayBound
    /\ RecoveryPathGoverned
    /\ ReorderedRequestSafe
    /\ NoDuplicateEffect
    /\ CurrentEpochAtCommit
    /\ FailSafeAdmissionHeld
    /\ NoPartitionedCommit
    /\ RecoveryIntentCoupled
    /\ TCBClosed
    /\ GuaranteeWithinCeiling
    /\ ProfileContractBound

=============================================================================
