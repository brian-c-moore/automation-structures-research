---- MODULE ALKClaimAuthorityExecutionWitness ----
EXTENDS ALKClaimAuthorityWitness

VARIABLES authorityMode, lastMode, lastActor, lastDecision, lastBehavior,
          lastKind, lastIssuer, priorBudget, priorSequential

executionVars ==
    <<vars, authorityMode, lastMode, lastActor, lastDecision, lastBehavior,
      lastKind, lastIssuer, priorBudget, priorSequential>>

FrameForBehavior(behavior) ==
    IF behavior \in BudgetBehaviors THEN BudgetFrame ELSE SequentialFrame

IssuerForBehavior(mode, behavior) ==
    LET frame == FrameForBehavior(behavior)
        owners == OwnersOf(frame, Principals, DerivedOwnership(mode))
    IN IF owners = {} THEN "none"
       ELSE CanonicalOwner(frame, Principals, DerivedOwnership(mode))

ExecutionInit ==
    /\ Init
    /\ authorityMode = "direct"
    /\ lastMode = "direct"
    /\ lastActor = "job-controller"
    /\ lastDecision = {}
    /\ lastBehavior = "initial"
    /\ lastKind = "initial"
    /\ lastIssuer = "none"
    /\ priorBudget = budgetVars
    /\ priorSequential = sequentialVars

RecordExecution(actor, decision, behavior, kind) ==
    /\ lastMode' = authorityMode
    /\ lastActor' = actor
    /\ lastDecision' = decision
    /\ lastBehavior' = behavior
    /\ lastKind' = kind
    /\ lastIssuer' =
         IF kind = "commit" THEN IssuerForBehavior(authorityMode, behavior)
         ELSE "none"
    /\ priorBudget' = budgetVars
    /\ priorSequential' = sequentialVars
    /\ UNCHANGED authorityMode

ExecuteBehavior(behavior) ==
    LET actor == ControllerOfBehavior(authorityMode, behavior)
        decision == RequiredDecision(authorityMode, behavior)
    IN /\ AuthorizedBehaviorStep(authorityMode, actor, decision, behavior)
       /\ RecordExecution(actor, decision, behavior, "commit")

ConfigureAuthority(mode) ==
    /\ authorityMode = "direct"
    /\ mode \in AuthorityModes \ {"direct"}
    /\ authorityMode' = mode
    /\ lastKind' = "configuration"
    /\ UNCHANGED <<vars, lastMode, lastActor, lastDecision, lastBehavior,
                   lastIssuer, priorBudget, priorSequential>>

DelegateWork ==
    /\ authorityMode = "work"
    /\ UNCHANGED vars
    /\ RecordExecution("budget-worker", {}, "worker-compute", "work")

RejectFormerOwner ==
    /\ authorityMode = "transfer"
    /\ ~AuthorizationValid(
           authorityMode, "budget-authority", {"budget-authority"},
           "budget-try-allocate")
    /\ UNCHANGED vars
    /\ RecordExecution(
           "budget-authority", {"budget-authority"},
           "budget-try-allocate", "rejected")

ExecutionNext ==
    \/ \E behavior \in CatalogBehaviors : ExecuteBehavior(behavior)
    \/ \E mode \in AuthorityModes : ConfigureAuthority(mode)
    \/ DelegateWork
    \/ RejectFormerOwner

ExecutionSpec == ExecutionInit /\ [][ExecutionNext]_executionVars

ExecutionTypeHeld ==
    /\ BudgetTypeHolds
    /\ SequentialTypeHolds
    /\ authorityMode \in AuthorityModes
    /\ lastMode \in AuthorityModes
    /\ lastActor \in Principals
    /\ lastDecision \subseteq Principals
    /\ lastBehavior \in Behaviors \cup {"initial"}
    /\ lastKind \in {"initial", "configuration", "commit", "work", "rejected"}
    /\ lastIssuer \in Principals \cup {"none"}

CommitAuthorizationHeld ==
    lastKind = "commit" =>
      AuthorizationValid(lastMode, lastActor, lastDecision, lastBehavior)

IssuedClaimHeld ==
    lastKind = "commit" =>
      LET frame == FrameForBehavior(lastBehavior)
          owners == OwnersOf(frame, Principals, DerivedOwnership(lastMode))
      IN /\ lastIssuer = IssuerForBehavior(lastMode, lastBehavior)
         /\ (lastIssuer # "none" =>
               /\ lastIssuer \in owners
               /\ FramePredicateHolds[frame])
         /\ (owners = {} => lastIssuer = "none")

ExecutionFrameHeld ==
    /\ (lastKind = "commit" /\ lastBehavior \in BudgetBehaviors
          => sequentialVars = priorSequential)
    /\ (lastKind = "commit" /\ lastBehavior \in SequentialBehaviors \cup {"sequential-done"}
          => budgetVars = priorBudget)
    /\ (lastKind \in {"work", "rejected"}
          => /\ budgetVars = priorBudget
             /\ sequentialVars = priorSequential
             /\ lastIssuer = "none")
    /\ (lastKind = "rejected"
          => ~AuthorizationValid(lastMode, lastActor, lastDecision, lastBehavior))

ExecutionInvariant ==
    /\ ExecutionTypeHeld
    /\ ClaimInstantiationHeld
    /\ CommitAuthorizationHeld
    /\ IssuedClaimHeld
    /\ ExecutionFrameHeld
    /\ \A mode \in AuthorityModes :
          OwnershipBoundaryHeld(DerivedOwnership(mode), ControlsForMode(mode))

====
