---- MODULE ALKClaimAuthorityBinding_Proof ----
EXTENDS ALKClaimAuthorityBinding, ALKClaimInstantiation_Proof

THEOREM MechanismControllerBindingTyped ==
    \A mode \in AuthorityModes :
      \A behavior \in CatalogBehaviors :
        /\ MechanismOfBehavior(mode, behavior) \in Mechanisms
        /\ ControllerOfBehavior(mode, behavior) \in Principals
        /\ RequiredDecision(mode, behavior) \subseteq Principals
BY SMT DEF MechanismOfBehavior, ControllerOfBehavior, RequiredDecision,
           MechanismController, Mechanisms, Principals, ProtocolMembers

THEOREM ControllerCanPerformBoundAction ==
    \A mode \in AuthorityModes :
      \A behavior \in CatalogBehaviors :
        BoundBehaviorStep(behavior) <=>
          AuthorizedBehaviorStep(
              mode, ControllerOfBehavior(mode, behavior),
              RequiredDecision(mode, behavior), behavior)
BY SMT, MechanismControllerBindingTyped
   DEF AuthorizedBehaviorStep, AuthorizationValid

THEOREM GuardedActionBindingExact ==
    \A mode \in AuthorityModes : GuardedNext(mode) <=> Next
BY SMT, ControllerCanPerformBoundAction, CatalogActionBindingExact
   DEF GuardedNext, BoundNext

THEOREM AuthorizedBehaviorPreservesCatalog ==
    \A mode \in AuthorityModes :
      \A actor \in Principals :
        \A decision \in SUBSET Principals :
          \A behavior \in CatalogBehaviors :
            ProductInvariant /\ AuthorizedBehaviorStep(mode, actor, decision, behavior)
              => ProductInvariant'
BY SMT, BoundBehaviorSafety DEF AuthorizedBehaviorStep

THEOREM UnboundControllerCannotCommit ==
    \A mode \in AuthorityModes :
      \A actor \in Principals :
        \A decision \in SUBSET Principals :
          \A behavior \in CatalogBehaviors :
            actor # ControllerOfBehavior(mode, behavior)
              => ~AuthorizedBehaviorStep(mode, actor, decision, behavior)
BY DEF AuthorizedBehaviorStep, AuthorizationValid

THEOREM PartialProtocolDecisionCannotCommit ==
    \A actor \in Principals :
      \A decision \in SUBSET Principals :
        \A behavior \in BudgetBehaviors :
          decision # ProtocolMembers
            => ~AuthorizedBehaviorStep("protocol", actor, decision, behavior)
BY SMT DEF AuthorizedBehaviorStep, AuthorizationValid, RequiredDecision

THEOREM DerivedOwnerHasDecisiveControl ==
    \A mode \in AuthorityModes :
      \A pair \in DerivedOwnership(mode) :
        /\ pair[2] \in AccountabilityNominees(mode, pair[1])
        /\ \A behavior \in DecisiveOf[pair[1]] :
              ControllerOfBehavior(mode, behavior) = pair[2]
BY SMT DEF DerivedOwnership, EligibleOwners, Covers, ControlsForMode, ExcludesOf

====
