---- MODULE ALKClaimFrameData ----
EXTENDS Naturals, Sequences, ALKRetainedRegistryData, ClaimRelativeOwnership

\* Static definition authority shared by the live instance and certificate.
SelectedStructureSchemas == {"AS-BUD-CAP"}
SelectedExecutionSchemas == {"EX-SEQ-SERIAL"}
SelectedSchemas == SelectedStructureSchemas \cup SelectedExecutionSchemas

SelectedStructureClauseOccurrences ==
    UNION {RegistrySchemaClauses[schema] :
              schema \in SelectedStructureSchemas}

SelectedExecutionClauseOccurrences ==
    UNION {RegistrySchemaClauses[schema] :
              schema \in SelectedExecutionSchemas}

SelectedClauseOccurrences ==
    SelectedStructureClauseOccurrences
      \cup SelectedExecutionClauseOccurrences

BudgetFrame ==
    [subject |-> "bounded-job",
     obligation |-> "AS-BUD-CAP",
     mode |-> "default",
     scope |-> "one-capacity-two-ledger",
     observationBoundary |-> "complete-budget-ledger-state",
     authorityBoundary |-> "complete-budget-ledger-writer-boundary",
     claimant |-> "job-controller",
     failureModel |-> "in-memory-no-crash-no-hidden-writer",
     abstraction |-> "budget-ledger",
     lifecyclePhase |-> "execution",
     propertyForm |-> "safety"]

SequentialFrame ==
    [subject |-> "bounded-job",
     obligation |-> "EX-SEQ-SERIAL",
     mode |-> "default",
     scope |-> "one-two-step-sequence",
     observationBoundary |-> "complete-cursor-active-value-history-state",
     authorityBoundary |-> "complete-sequential-carrier-writer-boundary",
     claimant |-> "job-controller",
     failureModel |-> "in-memory-no-crash-no-hidden-writer",
     abstraction |-> "sequential-carrier",
     lifecyclePhase |-> "execution",
     propertyForm |-> "safety"]

Frames == {BudgetFrame, SequentialFrame}
Subjects == {"bounded-job"}
ObligationSchemas == SelectedSchemas
Modes == {"default"}
Scopes == {frame.scope : frame \in Frames}
ObservationBoundaries ==
    {frame.observationBoundary : frame \in Frames}
AuthorityBoundaries == {frame.authorityBoundary : frame \in Frames}
Claimants == {"job-controller"}
FailureModels == {"in-memory-no-crash-no-hidden-writer"}
Abstractions == {frame.abstraction : frame \in Frames}
LifecyclePhases == {"execution"}

FrameOfSchema ==
    [schema \in SelectedSchemas |->
        IF schema = "AS-BUD-CAP" THEN BudgetFrame ELSE SequentialFrame]

BudgetBehaviors ==
    {"budget-try-allocate", "budget-reserve",
     "budget-commit-reservation", "budget-release",
     "budget-mark-eviction", "budget-complete-eviction"}

SequentialBehaviors == {"sequential-begin", "sequential-complete"}

DecisiveBehaviors == BudgetBehaviors \cup SequentialBehaviors

CatalogBehaviors == DecisiveBehaviors \cup {"sequential-done"}

DecisiveBehaviorOfSchema ==
    [schema \in SelectedSchemas |->
        IF schema = "AS-BUD-CAP"
          THEN BudgetBehaviors
        ELSE SequentialBehaviors]

AuthorityBoundaryBehaviorOfFrame ==
    [frame \in Frames |-> DecisiveBehaviorOfSchema[frame.obligation]]

FailureConditions ==
    {"over-capacity-ledger", "hidden-budget-writer", "arithmetic-overflow",
     "cursor-history-divergence", "hidden-sequential-writer",
     "crash-retry-or-durable-effect"}

FailureConditionsOfFrame ==
    [frame \in Frames |->
        IF frame = BudgetFrame
          THEN {"over-capacity-ledger", "hidden-budget-writer",
                "arithmetic-overflow", "crash-retry-or-durable-effect"}
        ELSE {"cursor-history-divergence", "hidden-sequential-writer",
              "crash-retry-or-durable-effect"}]

ObservedStateOfFrame ==
    [frame \in Frames |->
        IF frame = BudgetFrame
          THEN {"capacity", "allocated", "reserved", "pending-eviction"}
        ELSE {"cursor", "value", "active", "history"}]

====
