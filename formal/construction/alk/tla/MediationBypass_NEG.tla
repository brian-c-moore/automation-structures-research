---- MODULE MediationBypass_NEG ----
EXTENDS ALKSemanticModelWitness

BypassActions ==
    [action \in ActionLabels |->
        IF action = "bypass"
          THEN {<<"epoch-1", "failed-1">>}
        ELSE Actions[action]]

BypassPathClassOf ==
    [claim \in Claims |->
        [action \in ActionLabels |->
            IF action = "debug-path"
              THEN "excluded"
            ELSE IF action = "bypass"
              THEN "bypass"
            ELSE IF action \in {"external-store", "external-owner-failure"}
              THEN "external"
            ELSE "mediated"]]

BypassAdmittedActions ==
    [claim \in Claims |->
        ClaimActions[claim]
          \ ExcludedActionsFor(claim, ClaimActions, BypassPathClassOf)]

BypassViolatingActions ==
    [obligation \in Obligations |->
        ExpectedViolatingActionsFor(
            obligation, States, ActionLabels, BypassActions,
            ObligationPropertyClass,
            ObligationStates, ViolationStates,
            AllowedRelationSteps)]

BypassRelevantActions ==
    [claim \in Claims |->
        {"commit"}
          \cup (BypassAdmittedActions[claim]
                  \cap SelectedGovernanceActionsFor(
                           claim, ClaimObligations,
                           ObligationPropertyClass,
                           BypassViolatingActions,
                           LivenessProgressActions))]

CompleteMediationHeld ==
    /\ MediationBoundaryTyped(
           States, Claims, Obligations, ActionLabels, BypassActions,
           ClaimActions, BypassAdmittedActions,
           ClaimObligations, ObligationPropertyClass,
           BypassViolatingActions, LivenessProgressActions,
           BypassRelevantActions, BypassPathClassOf)
    /\ \A claim \in Claims :
          CompleteMediation(
              claim, ClaimActions,
              BypassRelevantActions, BypassPathClassOf)

NegativeControlExpected == NegativeControlGate(CompleteMediationHeld)

====
