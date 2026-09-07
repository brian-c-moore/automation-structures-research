---- MODULE ExcludedPathInhabited_NEG ----
EXTENDS ALKSemanticModelWitness

InhabitedExcludedActions ==
    [action \in ActionLabels |->
        IF action = "debug-path"
          THEN {<<"epoch-1", "failed-1">>}
        ELSE Actions[action]]

ExcludedPathAbsenceHeld ==
    MediationBoundaryTyped(
        States, Claims, Obligations, ActionLabels,
        InhabitedExcludedActions,
        ClaimActions, AdmittedActions, ClaimObligations,
        ObligationPropertyClass, ViolatingActions,
        LivenessProgressActions,
        ObligationRelevantActions, PathClassOf)

NegativeControlExpected == NegativeControlGate(ExcludedPathAbsenceHeld)

====
