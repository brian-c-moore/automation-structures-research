---- MODULE MediationNoEnforcement_NEG ----
EXTENDS ALKConstructionTheoremWitness

UnconstrainedGovernedPostMediationSteps ==
    [action \in ActionLabels |->
        IF action = "fault"
          THEN PotentialActions["fault"]
          ELSE PostMediationSteps[action]]
UnconstrainedGovernedFormalStepsForClaim ==
    [claim \in Claims |->
        ActionUnion(AdmittedActions[claim],
                    UnconstrainedGovernedPostMediationSteps)]

GovernedMediationEnforcementHeld ==
    MediationEnforcementPremises(
        States, Claims, Obligations, ActionLabels,
        AdmittedActions, GovernedActions,
        ClaimObligations, ObligationStates,
        UnconstrainedGovernedPostMediationSteps,
        UnconstrainedGovernedFormalStepsForClaim)

ReclassifiedPostMediationSteps ==
    [action \in ActionLabels |->
        IF action = "shared"
          THEN {<<"open", "bad">>}
          ELSE PostMediationSteps[action]]
ReclassifiedFormalStepsForClaim ==
    [claim \in Claims |->
        ActionUnion(AdmittedActions[claim],
                    ReclassifiedPostMediationSteps)]

NongovernedReclassificationHeld ==
    MediationEnforcementPremises(
        States, Claims, Obligations, ActionLabels,
        AdmittedActions, GovernedActions,
        ClaimObligations, ObligationStates,
        ReclassifiedPostMediationSteps,
        ReclassifiedFormalStepsForClaim)

MutantMediationEnforcementHeld ==
    GovernedMediationEnforcementHeld
      \/ NongovernedReclassificationHeld

NegativeControlExpected == NegativeControlGate(MutantMediationEnforcementHeld)

====
