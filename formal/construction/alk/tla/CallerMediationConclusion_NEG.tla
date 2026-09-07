---- MODULE CallerMediationConclusion_NEG ----
EXTENDS ALKConstructionTheoremWitness

CallerAdvertisedCompleteMediation == TRUE
MutantPathClassOf ==
    [claim \in Claims |->
        [action \in ActionLabels |->
            IF action = "fault" THEN "bypass" ELSE PathClassOf[claim][action]]]

DerivedMediationHeld ==
    /\ CallerAdvertisedCompleteMediation
    /\ GovernedCommitMediationPremises(
           States, Claims, Obligations, ActionLabels,
           PotentialActions, Actors,
           ClaimActions, AdmittedActions,
           ClaimObligations, ObligationPropertyClass,
           ViolatingActions, LivenessProgressActions,
           ObligationRelevantActions, MutantPathClassOf,
           GovernedCommitSteps, ClaimCommitActions,
           GovernedActions, OwnerOf, ALKAuthority)

NegativeControlExpected == NegativeControlGate(DerivedMediationHeld)

====
