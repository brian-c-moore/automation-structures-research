---- MODULE ALKProfiles ----
EXTENDS ALKConstructionTheorem

ProfileNames ==
    {"local-reference", "modular", "delegated", "bounded-distributed"}

ExpectedProfileStructures(profile) ==
    CASE profile \in {"local-reference", "modular", "delegated"} ->
           {"Budget", "ResourceRegistry", "ActuationPass", "AuditSink"}
      [] profile = "bounded-distributed" ->
           {"Budget", "ResourceRegistry", "ActuationPass", "AuditSink",
            "FederatedBudget"}

ExpectedProfileExecutionModality(profile) ==
    CASE profile = "local-reference" -> "Sequential"
      [] profile = "modular" -> "StepGraph"
      [] profile = "delegated" -> "Sequential"
      [] profile = "bounded-distributed" -> "ForkJoin"

ExpectedProfileCommitOwner(profile) ==
    CASE profile = "delegated" -> "external-owner"
      [] profile = "bounded-distributed" -> "cluster-owner"
      [] OTHER -> "builder"

ExpectedProfileProcessBoundaries(profile) ==
    CASE profile = "local-reference" -> {"alk-process"}
      [] profile = "modular" -> {"module-a", "module-b"}
      [] profile = "delegated" ->
           {"alk-process", "external-owner-boundary"}
      [] profile = "bounded-distributed" ->
           {"node-a", "node-b", "node-c"}

ExpectedProfileProcessOwner(profile) ==
    [boundary \in ExpectedProfileProcessBoundaries(profile) |->
        CASE profile = "delegated"
               /\ boundary = "external-owner-boundary" ->
             "external-owner"
          [] profile = "bounded-distributed" -> "cluster-owner"
          [] OTHER -> "builder"]

ExpectedProfileComponentPlacement(profile) ==
    [component \in CompositionComponents |->
        CASE profile = "local-reference" -> "alk-process"
          [] profile = "modular" ->
               IF component = "component-a" THEN "module-a" ELSE "module-b"
          [] profile = "delegated" ->
               IF component = "component-a"
                 THEN "alk-process"
                 ELSE "external-owner-boundary"
          [] OTHER ->
               IF component = "component-a" THEN "node-b" ELSE "node-c"]

ProfileSelectionBoundaryTyped(
        profile, Structures, ExecutionModalities,
        SelectedStructures, SelectedExecutionModality) ==
    /\ profile \in ProfileNames
    /\ SelectedStructures \in SUBSET Structures
    /\ SelectedStructures = ExpectedProfileStructures(profile)
    /\ SelectedExecutionModality \in ExecutionModalities
    /\ SelectedExecutionModality =
         ExpectedProfileExecutionModality(profile)

ProfileTopologyBoundaryTyped(
        profile, Actors, ProcessBoundaries, ProcessOwner,
        ComponentPlacement, CommitOwner) ==
    /\ profile \in ProfileNames
    /\ CommitOwner \in Actors
    /\ ProcessBoundaries = ExpectedProfileProcessBoundaries(profile)
    /\ ProcessOwner = ExpectedProfileProcessOwner(profile)
    /\ ProcessOwner \in [ProcessBoundaries -> Actors]
    /\ ComponentPlacement = ExpectedProfileComponentPlacement(profile)
    /\ ComponentPlacement
         \in [CompositionComponents -> ProcessBoundaries]
    /\ CommitOwner = ExpectedProfileCommitOwner(profile)
    /\ CASE profile = "local-reference" ->
              /\ ProcessBoundaries = {"alk-process"}
              /\ ProcessOwner["alk-process"] = CommitOwner
          [] profile = "modular" ->
              /\ ProcessBoundaries = {"module-a", "module-b"}
              /\ ComponentPlacement["component-a"] #
                   ComponentPlacement["component-b"]
          [] profile = "delegated" ->
              /\ "external-owner-boundary" \in ProcessBoundaries
              /\ ProcessOwner["external-owner-boundary"] = CommitOwner
          [] profile = "bounded-distributed" ->
              /\ ProcessBoundaries = {"node-a", "node-b", "node-c"}
              /\ \A boundary \in ProcessBoundaries :
                    ProcessOwner[boundary] = CommitOwner

RelationSources(Relation) == {pair[1] : pair \in Relation}
RelationTargets(Relation) == {pair[2] : pair \in Relation}

DistributedExecutionBoundaryTyped(
        S, MembershipOf, EpochOf, PartitionedStates,
        ReconfigurationSteps, RetrySteps, PartitionSteps,
        RecoverySteps, CollectiveCommitSteps) ==
    /\ RelationTyped(S, PartitionSteps)
    /\ ReconfigurationSteps # {}
    /\ RetrySteps # {}
    /\ PartitionSteps # {}
    /\ RecoverySteps # {}
    /\ CollectiveCommitSteps # {}
    /\ \A pair \in ReconfigurationSteps :
          /\ EpochOf[pair[2]] # EpochOf[pair[1]]
          /\ MembershipOf[pair[2]] # MembershipOf[pair[1]]
    /\ RelationSources(RetrySteps)
         = RelationTargets(ReconfigurationSteps)
    /\ RelationTargets(RetrySteps)
         = RelationTargets(ReconfigurationSteps)
    /\ RelationSources(PartitionSteps)
         = RelationTargets(ReconfigurationSteps)
    /\ RelationTargets(PartitionSteps) = PartitionedStates
    /\ RelationSources(RecoverySteps) = PartitionedStates
    /\ RelationTargets(RecoverySteps)
         = RelationTargets(ReconfigurationSteps)
    /\ RelationSources(CollectiveCommitSteps)
         = RelationTargets(RecoverySteps)

ProfileFailureScenarioCeiling(failureClass, NormalBundle) ==
    DerivedFailureCeiling(
        failureClass, NormalBundle,
        failureClass # "bypass",
        failureClass # "partition",
        failureClass # "stale-epoch",
        failureClass # "assurance-loss",
        failureClass # "audit-loss",
        failureClass # "external-owner",
        failureClass # "retry-exhaustion",
        failureClass # "recovery-failure")

ExpectedProfileFailureCeiling(failureClass) ==
    CASE failureClass = "bypass" -> {"lost"}
      [] failureClass = "partition" -> {"conditional"}
      [] failureClass = "stale-epoch" -> {"lost"}
      [] failureClass = "assurance-loss" -> {"conditional"}
      [] failureClass = "audit-loss" ->
           {"prevention", "conditional"}
      [] failureClass = "external-owner" ->
           {"detection", "recovery", "conditional"}
      [] failureClass = "retry-exhaustion" -> {"conditional"}
      [] OTHER -> {"prevention", "detection", "conditional"}

ExactProfileFailureLedger(NormalBundle, FailureLedger) ==
    /\ NormalBundle =
         {"prevention", "detection", "recovery", "conditional"}
    /\ FailureLedger \in [ALKFailureClasses -> SUBSET GuaranteeKinds]
    /\ \A failureClass \in ALKFailureClasses :
          /\ FailureLedger[failureClass] =
               ProfileFailureScenarioCeiling(failureClass, NormalBundle)
          /\ FailureLedger[failureClass] =
               ExpectedProfileFailureCeiling(failureClass)

\* The builder receives the claim, external-owner owns and guarantees the
\* commit, and assurer is inside the owner's precommit enforcement path.
DelegatedPrecommitCeiling ==
    GuaranteeCeiling(
        "builder", "external-owner", "assurer", "precommit",
        {"assurer"}, {}, TRUE, TRUE)

DelegatedPostcommitCeiling ==
    GuaranteeCeiling(
        "builder", "external-owner", "assurer", "postcommit",
        {}, {}, TRUE, TRUE)

DelegatedUnavailableCeiling ==
    GuaranteeCeiling(
        "builder", "external-owner", "assurer", "precommit",
        {"assurer"}, {"assurer"}, TRUE, TRUE)

DelegatedVariantCeilingsExact ==
    /\ DelegatedPrecommitCeiling =
         {"prevention", "conditional", "lost"}
    /\ DelegatedPostcommitCeiling =
         {"detection", "recovery", "conditional", "lost"}
    /\ "prevention" \notin DelegatedPostcommitCeiling
    /\ DelegatedUnavailableCeiling = {"conditional", "lost"}

====
