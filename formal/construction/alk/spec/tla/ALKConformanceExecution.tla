------------------ MODULE ALKConformanceExecution ------------------
EXTENDS ALKReferenceStateMachine

VARIABLES vectorName, vectorStep

ExecutableVectorNames ==
    {"positive.atomic-commit",
     "negative.assurance-unavailable",
     "negative.retry-exhaustion",
     "positive.partial-persistence-recovery",
     "positive.same-request-duplicate",
     "negative.conflicting-duplicate",
     "positive.lost-response-retry",
     "negative.stale-replay",
     "negative.stale-read",
     "negative.reordered-request",
     "negative.crash-before-check",
     "negative.crash-between-check-and-commit",
     "positive.crash-after-effect",
     "positive.crash-before-evidence",
     "positive.crash-after-commit",
     "negative.partitioned-commit",
     "positive.partition-heal-retry",
     "negative.external-owner-unavailable",
     "positive.audit-loss-recovery",
     "positive.governed-configuration-local-reference-at-commit",
     "positive.governed-configuration-modular-at-commit",
     "positive.governed-configuration-delegated-at-commit",
     "positive.governed-configuration-delegated-precommit",
     "positive.governed-configuration-delegated-postcommit",
     "negative.governed-configuration-delegated-unavailable",
     "positive.governed-configuration-bounded-distributed-at-commit"}

CompatibleVectorNames(profile, mode) ==
    CASE /\ profile = "local-reference"
           /\ mode = "at-commit" ->
             {"positive.atomic-commit",
              "negative.retry-exhaustion",
              "positive.partial-persistence-recovery",
              "positive.same-request-duplicate",
              "negative.conflicting-duplicate",
              "positive.lost-response-retry",
              "negative.stale-replay",
              "negative.stale-read",
              "negative.reordered-request",
              "negative.crash-before-check",
              "negative.crash-between-check-and-commit",
              "positive.crash-after-effect",
              "positive.crash-before-evidence",
              "positive.crash-after-commit",
              "positive.audit-loss-recovery",
              "positive.governed-configuration-local-reference-at-commit"}
      [] /\ profile = "modular"
           /\ mode = "at-commit" ->
             {"positive.atomic-commit",
              "negative.retry-exhaustion",
              "positive.partial-persistence-recovery",
              "positive.same-request-duplicate",
              "negative.conflicting-duplicate",
              "positive.lost-response-retry",
              "negative.stale-replay",
              "negative.stale-read",
              "negative.reordered-request",
              "negative.crash-before-check",
              "negative.crash-between-check-and-commit",
              "positive.crash-after-effect",
              "positive.crash-before-evidence",
              "positive.crash-after-commit",
              "positive.audit-loss-recovery",
              "positive.governed-configuration-modular-at-commit"}
      [] /\ profile = "delegated"
           /\ mode = "at-commit" ->
             {"positive.atomic-commit",
              "negative.retry-exhaustion",
              "positive.partial-persistence-recovery",
              "positive.same-request-duplicate",
              "negative.conflicting-duplicate",
              "positive.lost-response-retry",
              "negative.stale-replay",
              "negative.stale-read",
              "negative.reordered-request",
              "negative.crash-before-check",
              "negative.crash-between-check-and-commit",
              "positive.crash-after-effect",
              "positive.crash-before-evidence",
              "positive.crash-after-commit",
              "negative.external-owner-unavailable",
              "positive.audit-loss-recovery",
              "positive.governed-configuration-delegated-at-commit"}
      [] /\ profile = "delegated"
           /\ mode = "precommit" ->
             {"positive.atomic-commit",
              "negative.retry-exhaustion",
              "positive.partial-persistence-recovery",
              "positive.same-request-duplicate",
              "negative.conflicting-duplicate",
              "positive.lost-response-retry",
              "negative.stale-replay",
              "negative.stale-read",
              "negative.reordered-request",
              "negative.crash-before-check",
              "negative.crash-between-check-and-commit",
              "positive.crash-after-effect",
              "positive.crash-before-evidence",
              "positive.crash-after-commit",
              "negative.external-owner-unavailable",
              "positive.audit-loss-recovery",
              "positive.governed-configuration-delegated-precommit"}
      [] /\ profile = "delegated"
           /\ mode = "postcommit" ->
             {"positive.atomic-commit",
              "negative.retry-exhaustion",
              "positive.partial-persistence-recovery",
              "positive.same-request-duplicate",
              "negative.conflicting-duplicate",
              "positive.lost-response-retry",
              "negative.stale-replay",
              "negative.stale-read",
              "negative.reordered-request",
              "negative.crash-before-check",
              "negative.crash-between-check-and-commit",
              "positive.crash-after-effect",
              "positive.crash-before-evidence",
              "positive.crash-after-commit",
              "negative.external-owner-unavailable",
              "positive.audit-loss-recovery",
              "positive.governed-configuration-delegated-postcommit"}
      [] /\ profile = "delegated"
           /\ mode = "unavailable" ->
             {"negative.assurance-unavailable",
              "negative.stale-replay",
              "negative.stale-read",
              "negative.crash-before-check",
              "negative.governed-configuration-delegated-unavailable"}
      [] /\ profile = "bounded-distributed"
           /\ mode = "at-commit" ->
             {"positive.atomic-commit",
              "negative.retry-exhaustion",
              "positive.partial-persistence-recovery",
              "positive.same-request-duplicate",
              "negative.conflicting-duplicate",
              "positive.lost-response-retry",
              "negative.stale-replay",
              "negative.stale-read",
              "negative.reordered-request",
              "negative.crash-before-check",
              "negative.crash-between-check-and-commit",
              "positive.crash-after-effect",
              "positive.crash-before-evidence",
              "positive.crash-after-commit",
              "negative.partitioned-commit",
              "positive.partition-heal-retry",
              "positive.audit-loss-recovery",
              "positive.governed-configuration-bounded-distributed-at-commit"}
      [] OTHER -> {}

VectorLength(name, profile, mode) ==
    CASE name = "positive.atomic-commit" ->
           CASE /\ profile = "bounded-distributed"
                  /\ mode = "at-commit" -> 4
             [] OTHER -> 3
      [] name = "negative.assurance-unavailable" -> 1
      [] name = "negative.retry-exhaustion" ->
           CASE /\ profile = "bounded-distributed"
                  /\ mode = "at-commit" -> 5
             [] OTHER -> 4
      [] name = "positive.partial-persistence-recovery" ->
           CASE /\ profile = "bounded-distributed"
                  /\ mode = "at-commit" -> 5
             [] OTHER -> 4
      [] name = "positive.same-request-duplicate" ->
           CASE /\ profile = "bounded-distributed"
                  /\ mode = "at-commit" -> 5
             [] OTHER -> 4
      [] name = "negative.conflicting-duplicate" ->
           CASE /\ profile = "bounded-distributed"
                  /\ mode = "at-commit" -> 5
             [] OTHER -> 4
      [] name = "positive.lost-response-retry" ->
           CASE /\ profile = "bounded-distributed"
                  /\ mode = "at-commit" -> 6
             [] OTHER -> 5
      [] name = "negative.stale-replay" -> 2
      [] name = "negative.stale-read" -> 2
      [] name = "negative.reordered-request" ->
           CASE /\ profile = "bounded-distributed"
                  /\ mode = "at-commit" -> 4
             [] OTHER -> 3
      [] name = "negative.crash-before-check" -> 2
      [] name = "negative.crash-between-check-and-commit" ->
           CASE /\ profile = "bounded-distributed"
                  /\ mode = "at-commit" -> 7
             [] OTHER -> 6
      [] name = "positive.crash-after-effect" ->
           CASE /\ profile = "bounded-distributed"
                  /\ mode = "at-commit" -> 7
             [] OTHER -> 6
      [] name = "positive.crash-before-evidence" ->
           CASE /\ profile = "bounded-distributed"
                  /\ mode = "at-commit" -> 7
             [] OTHER -> 6
      [] name = "positive.crash-after-commit" ->
           CASE /\ profile = "bounded-distributed"
                  /\ mode = "at-commit" -> 7
             [] OTHER -> 6
      [] name = "negative.partitioned-commit" ->
           CASE /\ profile = "bounded-distributed"
                  /\ mode = "at-commit" -> 5
             [] OTHER -> 4
      [] name = "positive.partition-heal-retry" ->
           CASE /\ profile = "bounded-distributed"
                  /\ mode = "at-commit" -> 6
             [] OTHER -> 5
      [] name = "negative.external-owner-unavailable" -> 3
      [] name = "positive.audit-loss-recovery" ->
           CASE /\ profile = "bounded-distributed"
                  /\ mode = "at-commit" -> 6
             [] OTHER -> 5
      [] name = "positive.governed-configuration-local-reference-at-commit" -> 4
      [] name = "positive.governed-configuration-modular-at-commit" -> 4
      [] name = "positive.governed-configuration-delegated-at-commit" -> 4
      [] name = "positive.governed-configuration-delegated-precommit" -> 4
      [] name = "positive.governed-configuration-delegated-postcommit" -> 4
      [] name = "negative.governed-configuration-delegated-unavailable" -> 2
      [] name = "positive.governed-configuration-bounded-distributed-at-commit" -> 4
      [] OTHER -> 0

VectorAction(name, profile, mode, step) ==
    CASE name = "positive.atomic-commit" ->
           CASE /\ profile = "bounded-distributed"
                  /\ mode = "at-commit" ->
                    CASE step = 0 -> GovernedConfigurationUpdate
                      [] step = 1 -> Admit
                      [] step = 2 -> PrepareEffect
                      [] step = 3 -> CommitAtomic
                      [] OTHER -> FALSE
             [] OTHER ->
                  CASE step = 0 -> Admit
                    [] step = 1 -> PrepareEffect
                    [] step = 2 -> CommitAtomic
                    [] OTHER -> FALSE
      [] name = "negative.assurance-unavailable" ->
           CASE step = 0 -> RejectUnavailableAssurance
             [] OTHER -> FALSE
      [] name = "negative.retry-exhaustion" ->
           CASE /\ profile = "bounded-distributed"
                  /\ mode = "at-commit" ->
                    CASE step = 0 -> GovernedConfigurationUpdate
                      [] step = 1 -> Admit
                      [] step = 2 -> PrepareEffect
                      [] step = 3 -> FailBeforeEffect
                      [] step = 4 -> FailBeforeEffect
                      [] OTHER -> FALSE
             [] OTHER ->
                  CASE step = 0 -> Admit
                    [] step = 1 -> PrepareEffect
                    [] step = 2 -> FailBeforeEffect
                    [] step = 3 -> FailBeforeEffect
                    [] OTHER -> FALSE
      [] name = "positive.partial-persistence-recovery" ->
           CASE /\ profile = "bounded-distributed"
                  /\ mode = "at-commit" ->
                    CASE step = 0 -> GovernedConfigurationUpdate
                      [] step = 1 -> Admit
                      [] step = 2 -> PrepareEffect
                      [] step = 3 -> ApplyEffectBeforeEvidence
                      [] step = 4 -> RecoverEvidence
                      [] OTHER -> FALSE
             [] OTHER ->
                  CASE step = 0 -> Admit
                    [] step = 1 -> PrepareEffect
                    [] step = 2 -> ApplyEffectBeforeEvidence
                    [] step = 3 -> RecoverEvidence
                    [] OTHER -> FALSE
      [] name = "positive.same-request-duplicate" ->
           CASE /\ profile = "bounded-distributed"
                  /\ mode = "at-commit" ->
                    CASE step = 0 -> GovernedConfigurationUpdate
                      [] step = 1 -> Admit
                      [] step = 2 -> PrepareEffect
                      [] step = 3 -> CommitAtomic
                      [] step = 4 -> DuplicateSameRequest
                      [] OTHER -> FALSE
             [] OTHER ->
                  CASE step = 0 -> Admit
                    [] step = 1 -> PrepareEffect
                    [] step = 2 -> CommitAtomic
                    [] step = 3 -> DuplicateSameRequest
                    [] OTHER -> FALSE
      [] name = "negative.conflicting-duplicate" ->
           CASE /\ profile = "bounded-distributed"
                  /\ mode = "at-commit" ->
                    CASE step = 0 -> GovernedConfigurationUpdate
                      [] step = 1 -> Admit
                      [] step = 2 -> PrepareEffect
                      [] step = 3 -> CommitAtomic
                      [] step = 4 -> ConflictingDuplicate
                      [] OTHER -> FALSE
             [] OTHER ->
                  CASE step = 0 -> Admit
                    [] step = 1 -> PrepareEffect
                    [] step = 2 -> CommitAtomic
                    [] step = 3 -> ConflictingDuplicate
                    [] OTHER -> FALSE
      [] name = "positive.lost-response-retry" ->
           CASE /\ profile = "bounded-distributed"
                  /\ mode = "at-commit" ->
                    CASE step = 0 -> GovernedConfigurationUpdate
                      [] step = 1 -> Admit
                      [] step = 2 -> PrepareEffect
                      [] step = 3 -> CommitAtomic
                      [] step = 4 -> LoseResponse
                      [] step = 5 -> RetryLostResponse
                      [] OTHER -> FALSE
             [] OTHER ->
                  CASE step = 0 -> Admit
                    [] step = 1 -> PrepareEffect
                    [] step = 2 -> CommitAtomic
                    [] step = 3 -> LoseResponse
                    [] step = 4 -> RetryLostResponse
                    [] OTHER -> FALSE
      [] name = "negative.stale-replay" ->
           CASE step = 0 -> GovernedConfigurationUpdate
             [] step = 1 -> ReplayStaleRequest
             [] OTHER -> FALSE
      [] name = "negative.stale-read" ->
           CASE step = 0 -> GovernedConfigurationUpdate
             [] step = 1 -> ReadStaleState
             [] OTHER -> FALSE
      [] name = "negative.reordered-request" ->
           CASE /\ profile = "bounded-distributed"
                  /\ mode = "at-commit" ->
                    CASE step = 0 -> GovernedConfigurationUpdate
                      [] step = 1 -> Admit
                      [] step = 2 -> PrepareEffect
                      [] step = 3 -> RejectReorderedRequest
                      [] OTHER -> FALSE
             [] OTHER ->
                  CASE step = 0 -> Admit
                    [] step = 1 -> PrepareEffect
                    [] step = 2 -> RejectReorderedRequest
                    [] OTHER -> FALSE
      [] name = "negative.crash-before-check" ->
           CASE step = 0 -> CrashBeforeCheck
             [] step = 1 -> Restart
             [] OTHER -> FALSE
      [] name = "negative.crash-between-check-and-commit" ->
           CASE /\ profile = "bounded-distributed"
                  /\ mode = "at-commit" ->
                    CASE step = 0 -> GovernedConfigurationUpdate
                      [] step = 1 -> Admit
                      [] step = 2 -> PrepareEffect
                      [] step = 3 -> CrashBetweenCheckAndCommit
                      [] step = 4 -> Restart
                      [] step = 5 -> FailBeforeEffect
                      [] step = 6 -> FailBeforeEffect
                      [] OTHER -> FALSE
             [] OTHER ->
                  CASE step = 0 -> Admit
                    [] step = 1 -> PrepareEffect
                    [] step = 2 -> CrashBetweenCheckAndCommit
                    [] step = 3 -> Restart
                    [] step = 4 -> FailBeforeEffect
                    [] step = 5 -> FailBeforeEffect
                    [] OTHER -> FALSE
      [] name = "positive.crash-after-effect" ->
           CASE /\ profile = "bounded-distributed"
                  /\ mode = "at-commit" ->
                    CASE step = 0 -> GovernedConfigurationUpdate
                      [] step = 1 -> Admit
                      [] step = 2 -> PrepareEffect
                      [] step = 3 -> ApplyEffectBeforeEvidence
                      [] step = 4 -> CrashAfterEffect
                      [] step = 5 -> Restart
                      [] step = 6 -> RecoverEvidence
                      [] OTHER -> FALSE
             [] OTHER ->
                  CASE step = 0 -> Admit
                    [] step = 1 -> PrepareEffect
                    [] step = 2 -> ApplyEffectBeforeEvidence
                    [] step = 3 -> CrashAfterEffect
                    [] step = 4 -> Restart
                    [] step = 5 -> RecoverEvidence
                    [] OTHER -> FALSE
      [] name = "positive.crash-before-evidence" ->
           CASE /\ profile = "bounded-distributed"
                  /\ mode = "at-commit" ->
                    CASE step = 0 -> GovernedConfigurationUpdate
                      [] step = 1 -> Admit
                      [] step = 2 -> PrepareEffect
                      [] step = 3 -> ApplyEffectBeforeEvidence
                      [] step = 4 -> CrashBeforeEvidencePublication
                      [] step = 5 -> Restart
                      [] step = 6 -> RecoverEvidence
                      [] OTHER -> FALSE
             [] OTHER ->
                  CASE step = 0 -> Admit
                    [] step = 1 -> PrepareEffect
                    [] step = 2 -> ApplyEffectBeforeEvidence
                    [] step = 3 -> CrashBeforeEvidencePublication
                    [] step = 4 -> Restart
                    [] step = 5 -> RecoverEvidence
                    [] OTHER -> FALSE
      [] name = "positive.crash-after-commit" ->
           CASE /\ profile = "bounded-distributed"
                  /\ mode = "at-commit" ->
                    CASE step = 0 -> GovernedConfigurationUpdate
                      [] step = 1 -> Admit
                      [] step = 2 -> PrepareEffect
                      [] step = 3 -> CommitAtomic
                      [] step = 4 -> CrashAfterCommit
                      [] step = 5 -> Restart
                      [] step = 6 -> DuplicateSameRequest
                      [] OTHER -> FALSE
             [] OTHER ->
                  CASE step = 0 -> Admit
                    [] step = 1 -> PrepareEffect
                    [] step = 2 -> CommitAtomic
                    [] step = 3 -> CrashAfterCommit
                    [] step = 4 -> Restart
                    [] step = 5 -> DuplicateSameRequest
                    [] OTHER -> FALSE
      [] name = "negative.partitioned-commit" ->
           CASE /\ profile = "bounded-distributed"
                  /\ mode = "at-commit" ->
                    CASE step = 0 -> GovernedConfigurationUpdate
                      [] step = 1 -> Admit
                      [] step = 2 -> PrepareEffect
                      [] step = 3 -> Partition
                      [] step = 4 -> RejectPartitionedCommit
                      [] OTHER -> FALSE
             [] OTHER ->
                  CASE step = 0 -> Admit
                    [] step = 1 -> PrepareEffect
                    [] step = 2 -> Partition
                    [] step = 3 -> RejectPartitionedCommit
                    [] OTHER -> FALSE
      [] name = "positive.partition-heal-retry" ->
           CASE /\ profile = "bounded-distributed"
                  /\ mode = "at-commit" ->
                    CASE step = 0 -> GovernedConfigurationUpdate
                      [] step = 1 -> Admit
                      [] step = 2 -> PrepareEffect
                      [] step = 3 -> Partition
                      [] step = 4 -> HealPartition
                      [] step = 5 -> CommitAtomic
                      [] OTHER -> FALSE
             [] OTHER ->
                  CASE step = 0 -> Admit
                    [] step = 1 -> PrepareEffect
                    [] step = 2 -> Partition
                    [] step = 3 -> HealPartition
                    [] step = 4 -> CommitAtomic
                    [] OTHER -> FALSE
      [] name = "negative.external-owner-unavailable" ->
           CASE step = 0 -> Admit
             [] step = 1 -> PrepareEffect
             [] step = 2 -> ExternalOwnerUnavailable
             [] OTHER -> FALSE
      [] name = "positive.audit-loss-recovery" ->
           CASE /\ profile = "bounded-distributed"
                  /\ mode = "at-commit" ->
                    CASE step = 0 -> GovernedConfigurationUpdate
                      [] step = 1 -> Admit
                      [] step = 2 -> PrepareEffect
                      [] step = 3 -> CommitAtomic
                      [] step = 4 -> LoseAuditAfterCommit
                      [] step = 5 -> RecoverEvidence
                      [] OTHER -> FALSE
             [] OTHER ->
                  CASE step = 0 -> Admit
                    [] step = 1 -> PrepareEffect
                    [] step = 2 -> CommitAtomic
                    [] step = 3 -> LoseAuditAfterCommit
                    [] step = 4 -> RecoverEvidence
                    [] OTHER -> FALSE
      [] name = "positive.governed-configuration-local-reference-at-commit" ->
           CASE step = 0 -> GovernedConfigurationUpdate
             [] step = 1 -> Admit
             [] step = 2 -> PrepareEffect
             [] step = 3 -> CommitAtomic
             [] OTHER -> FALSE
      [] name = "positive.governed-configuration-modular-at-commit" ->
           CASE step = 0 -> GovernedConfigurationUpdate
             [] step = 1 -> Admit
             [] step = 2 -> PrepareEffect
             [] step = 3 -> CommitAtomic
             [] OTHER -> FALSE
      [] name = "positive.governed-configuration-delegated-at-commit" ->
           CASE step = 0 -> GovernedConfigurationUpdate
             [] step = 1 -> Admit
             [] step = 2 -> PrepareEffect
             [] step = 3 -> CommitAtomic
             [] OTHER -> FALSE
      [] name = "positive.governed-configuration-delegated-precommit" ->
           CASE step = 0 -> GovernedConfigurationUpdate
             [] step = 1 -> Admit
             [] step = 2 -> PrepareEffect
             [] step = 3 -> CommitAtomic
             [] OTHER -> FALSE
      [] name = "positive.governed-configuration-delegated-postcommit" ->
           CASE step = 0 -> GovernedConfigurationUpdate
             [] step = 1 -> Admit
             [] step = 2 -> PrepareEffect
             [] step = 3 -> CommitAtomic
             [] OTHER -> FALSE
      [] name = "negative.governed-configuration-delegated-unavailable" ->
           CASE step = 0 -> GovernedConfigurationUpdate
             [] step = 1 -> RejectUnavailableAssurance
             [] OTHER -> FALSE
      [] name = "positive.governed-configuration-bounded-distributed-at-commit" ->
           CASE step = 0 -> GovernedConfigurationUpdate
             [] step = 1 -> Admit
             [] step = 2 -> PrepareEffect
             [] step = 3 -> CommitAtomic
             [] OTHER -> FALSE

VectorOutcome(name, profile, mode) ==
    CASE name = "positive.atomic-commit" ->
           /\ phase = "committed"
           /\ effectCount = 1
           /\ evidenceState = "durable"
           /\ clientResponse = "success"
      [] name = "negative.assurance-unavailable" ->
           /\ phase = "rejected"
           /\ effectCount = 0
           /\ clientResponse = "rejected"
           /\ lastFailure = "assurance-loss"
           /\ presentedEpoch = 1
      [] name = "negative.retry-exhaustion" ->
           /\ phase = "rejected"
           /\ effectCount = 0
           /\ clientResponse = "rejected"
           /\ lastFailure = "retry-exhaustion"
      [] name = "positive.partial-persistence-recovery" ->
           /\ phase = "committed"
           /\ effectCount = 1
           /\ evidenceState = "durable"
           /\ clientResponse = "success"
      [] name = "positive.same-request-duplicate" ->
           CASE /\ profile = "bounded-distributed"
                  /\ mode = "at-commit" ->
                    /\ phase = "committed"
                    /\ effectCount = 1
                    /\ clientResponse = "success"
                    /\ requestDigest = "digest-a"
                    /\ presentedDigest = "digest-a"
                    /\ presentedEpoch = 2
                    /\ requestOrder = 1
                    /\ presentedOrder = 1
             [] OTHER ->
                  /\ phase = "committed"
                  /\ effectCount = 1
                  /\ clientResponse = "success"
                  /\ requestDigest = "digest-a"
                  /\ presentedDigest = "digest-a"
                  /\ presentedEpoch = 1
                  /\ requestOrder = 1
                  /\ presentedOrder = 1
      [] name = "negative.conflicting-duplicate" ->
           CASE /\ profile = "bounded-distributed"
                  /\ mode = "at-commit" ->
                    /\ phase = "committed"
                    /\ effectCount = 1
                    /\ clientResponse = "conflict"
                    /\ lastFailure = "none"
                    /\ requestDigest = "digest-a"
                    /\ presentedDigest = "digest-b"
                    /\ presentedEpoch = 2
                    /\ requestOrder = 1
                    /\ presentedOrder = 1
             [] OTHER ->
                  /\ phase = "committed"
                  /\ effectCount = 1
                  /\ clientResponse = "conflict"
                  /\ lastFailure = "none"
                  /\ requestDigest = "digest-a"
                  /\ presentedDigest = "digest-b"
                  /\ presentedEpoch = 1
                  /\ requestOrder = 1
                  /\ presentedOrder = 1
      [] name = "positive.lost-response-retry" ->
           CASE /\ profile = "bounded-distributed"
                  /\ mode = "at-commit" ->
                    /\ phase = "committed"
                    /\ effectCount = 1
                    /\ evidenceState = "durable"
                    /\ clientResponse = "success"
                    /\ presentedEpoch = 2
             [] OTHER ->
                  /\ phase = "committed"
                  /\ effectCount = 1
                  /\ evidenceState = "durable"
                  /\ clientResponse = "success"
                  /\ presentedEpoch = 1
      [] name = "negative.stale-replay" ->
           /\ phase = "idle"
           /\ effectCount = 0
           /\ clientResponse = "stale"
           /\ lastFailure = "stale-epoch"
           /\ presentedEpoch = 1
           /\ epoch = 2
      [] name = "negative.stale-read" ->
           /\ phase = "idle"
           /\ effectCount = 0
           /\ clientResponse = "stale"
           /\ lastFailure = "stale-epoch"
      [] name = "negative.reordered-request" ->
           CASE /\ profile = "bounded-distributed"
                  /\ mode = "at-commit" ->
                    /\ phase = "prepared"
                    /\ effectCount = 0
                    /\ evidenceState = "none"
                    /\ clientResponse = "stale"
                    /\ lastFailure = "reordered"
                    /\ requestDigest = "digest-a"
                    /\ presentedDigest = "digest-a"
                    /\ presentedEpoch = 2
                    /\ requestOrder = 1
                    /\ presentedOrder = 0
             [] OTHER ->
                  /\ phase = "prepared"
                  /\ effectCount = 0
                  /\ evidenceState = "none"
                  /\ clientResponse = "stale"
                  /\ lastFailure = "reordered"
                  /\ requestDigest = "digest-a"
                  /\ presentedDigest = "digest-a"
                  /\ presentedEpoch = 1
                  /\ requestOrder = 1
                  /\ presentedOrder = 0
      [] name = "negative.crash-before-check" ->
           /\ phase = "idle"
           /\ operationId = "none"
           /\ effectCount = 0
           /\ clientResponse = "none"
           /\ lastFailure = "before-check"
      [] name = "negative.crash-between-check-and-commit" ->
           /\ phase = "rejected"
           /\ effectCount = 0
           /\ clientResponse = "rejected"
           /\ lastFailure = "retry-exhaustion"
      [] name = "positive.crash-after-effect" ->
           /\ phase = "committed"
           /\ effectCount = 1
           /\ evidenceState = "durable"
           /\ clientResponse = "success"
      [] name = "positive.crash-before-evidence" ->
           /\ phase = "committed"
           /\ effectCount = 1
           /\ evidenceState = "durable"
           /\ clientResponse = "success"
      [] name = "positive.crash-after-commit" ->
           /\ phase = "committed"
           /\ effectCount = 1
           /\ evidenceState = "durable"
           /\ clientResponse = "success"
      [] name = "negative.partitioned-commit" ->
           /\ phase = "rejected"
           /\ effectCount = 0
           /\ clientResponse = "rejected"
           /\ lastFailure = "partition"
      [] name = "positive.partition-heal-retry" ->
           /\ phase = "committed"
           /\ effectCount = 1
           /\ evidenceState = "durable"
           /\ clientResponse = "success"
      [] name = "negative.external-owner-unavailable" ->
           /\ phase = "rejected"
           /\ effectCount = 0
           /\ clientResponse = "rejected"
           /\ lastFailure = "external-owner"
      [] name = "positive.audit-loss-recovery" ->
           /\ phase = "committed"
           /\ effectCount = 1
           /\ evidenceState = "durable"
           /\ clientResponse = "success"
      [] name = "positive.governed-configuration-local-reference-at-commit" ->
           /\ configVersion = 2
           /\ ownerRevision = 2
           /\ guaranteeRevision = 2
           /\ tcbRevision = 2
           /\ epoch = 2
           /\ credentialEpoch = 2
           /\ configuredOwner = "builder-rotated"
           /\ configuredGuarantees = {"conditional", "detection", "prevention"}
           /\ configuredTCB = {"audit-store", "claim-configuration-v2", "configuration-store", "effect-provider", "identity-authority", "kernel-code", "recovery-store"}
           /\ membership = {"single-node"}
           /\ phase = "committed"
           /\ effectCount = 1
           /\ effectOwner = "builder-rotated"
           /\ clientResponse = "success"
      [] name = "positive.governed-configuration-modular-at-commit" ->
           /\ configVersion = 2
           /\ ownerRevision = 2
           /\ guaranteeRevision = 2
           /\ tcbRevision = 2
           /\ epoch = 2
           /\ credentialEpoch = 2
           /\ configuredOwner = "builder-rotated"
           /\ configuredGuarantees = {"conditional", "detection", "prevention"}
           /\ configuredTCB = {"audit-store", "claim-configuration-v2", "configuration-store", "effect-provider", "identity-authority", "kernel-code", "recovery-store"}
           /\ membership = {"single-node"}
           /\ phase = "committed"
           /\ effectCount = 1
           /\ effectOwner = "builder-rotated"
           /\ clientResponse = "success"
      [] name = "positive.governed-configuration-delegated-at-commit" ->
           /\ configVersion = 2
           /\ ownerRevision = 2
           /\ guaranteeRevision = 2
           /\ tcbRevision = 2
           /\ epoch = 2
           /\ credentialEpoch = 2
           /\ configuredOwner = "external-owner-rotated"
           /\ configuredGuarantees = {"conditional", "detection", "prevention"}
           /\ configuredTCB = {"audit-store", "claim-configuration-v2", "configuration-store", "effect-provider", "external-owner-adapter", "identity-authority", "kernel-code", "recovery-store"}
           /\ membership = {"single-node"}
           /\ phase = "committed"
           /\ effectCount = 1
           /\ effectOwner = "external-owner-rotated"
           /\ clientResponse = "success"
      [] name = "positive.governed-configuration-delegated-precommit" ->
           /\ configVersion = 2
           /\ ownerRevision = 2
           /\ guaranteeRevision = 2
           /\ tcbRevision = 2
           /\ epoch = 2
           /\ credentialEpoch = 2
           /\ configuredOwner = "external-owner-rotated"
           /\ configuredGuarantees = {"conditional"}
           /\ configuredTCB = {"audit-store", "claim-configuration-v2", "configuration-store", "effect-provider", "external-owner-adapter", "identity-authority", "kernel-code", "recovery-store"}
           /\ membership = {"single-node"}
           /\ phase = "committed"
           /\ effectCount = 1
           /\ effectOwner = "external-owner-rotated"
           /\ clientResponse = "success"
      [] name = "positive.governed-configuration-delegated-postcommit" ->
           /\ configVersion = 2
           /\ ownerRevision = 2
           /\ guaranteeRevision = 2
           /\ tcbRevision = 2
           /\ epoch = 2
           /\ credentialEpoch = 2
           /\ configuredOwner = "external-owner-rotated"
           /\ configuredGuarantees = {"conditional", "detection"}
           /\ configuredTCB = {"audit-store", "claim-configuration-v2", "configuration-store", "effect-provider", "external-owner-adapter", "identity-authority", "kernel-code", "recovery-store"}
           /\ membership = {"single-node"}
           /\ phase = "committed"
           /\ effectCount = 1
           /\ effectOwner = "external-owner-rotated"
           /\ clientResponse = "success"
      [] name = "negative.governed-configuration-delegated-unavailable" ->
           /\ configVersion = 2
           /\ ownerRevision = 2
           /\ guaranteeRevision = 2
           /\ tcbRevision = 2
           /\ epoch = 2
           /\ credentialEpoch = 2
           /\ configuredOwner = "external-owner-rotated"
           /\ configuredGuarantees = {}
           /\ configuredTCB = {"audit-store", "claim-configuration-v2", "configuration-store", "effect-provider", "external-owner-adapter", "identity-authority", "kernel-code", "recovery-store"}
           /\ membership = {"single-node"}
           /\ phase = "rejected"
           /\ effectCount = 0
           /\ effectOwner = "none"
           /\ clientResponse = "rejected"
           /\ lastFailure = "assurance-loss"
      [] name = "positive.governed-configuration-bounded-distributed-at-commit" ->
           /\ configVersion = 2
           /\ ownerRevision = 2
           /\ guaranteeRevision = 2
           /\ tcbRevision = 2
           /\ epoch = 2
           /\ credentialEpoch = 2
           /\ configuredOwner = "cluster-owner-rotated"
           /\ configuredGuarantees = {"conditional", "detection", "prevention"}
           /\ configuredTCB = {"audit-store", "claim-configuration-v2", "configuration-store", "effect-provider", "identity-authority", "kernel-code", "membership-store", "recovery-store", "scheduler"}
           /\ membership = {"node-b", "node-c"}
           /\ phase = "committed"
           /\ effectCount = 1
           /\ effectOwner = "cluster-owner-rotated"
           /\ clientResponse = "success"
      [] OTHER -> FALSE

vectorVars == <<vars, vectorName, vectorStep>>

VectorInit ==
    /\ Init
    /\ vectorName \in CompatibleVectorNames(Profile, AssuranceMode)
    /\ vectorStep = 0

VectorAdvance ==
    \/ /\ vectorStep <
            VectorLength(vectorName, Profile, AssuranceMode)
       /\ UNCHANGED progressState
       /\ VectorAction(vectorName, Profile, AssuranceMode, vectorStep)
       /\ PresentedEpochUpdate
       /\ ProfileBridgeUpdate
       /\ <<phase, phase'>> \in PathTransitions(lastPath')
       /\ vectorStep' = vectorStep + 1
       /\ UNCHANGED vectorName
    \/ /\ vectorStep =
            VectorLength(vectorName, Profile, AssuranceMode)
       /\ VectorOutcome(vectorName, Profile, AssuranceMode)
       /\ UNCHANGED vectorVars

VectorInvariant ==
    /\ vectorName \in CompatibleVectorNames(Profile, AssuranceMode)
    /\ vectorStep \in
         0..VectorLength(vectorName, Profile, AssuranceMode)
    /\ vectorStep =
         VectorLength(vectorName, Profile, AssuranceMode) =>
           VectorOutcome(vectorName, Profile, AssuranceMode)

=====================================================================
