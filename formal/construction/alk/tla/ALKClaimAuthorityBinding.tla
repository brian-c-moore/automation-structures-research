---- MODULE ALKClaimAuthorityBinding ----
EXTENDS ALKClaimInstantiationWitness, ALKClaimAuthorityModel

AuthorizedBehaviorStep(mode, actor, decision, behavior) ==
    /\ AuthorizationValid(mode, actor, decision, behavior)
    /\ BoundBehaviorStep(behavior)

GuardedNext(mode) ==
    \E behavior \in CatalogBehaviors :
      AuthorizedBehaviorStep(
          mode, ControllerOfBehavior(mode, behavior),
          RequiredDecision(mode, behavior), behavior)

====
