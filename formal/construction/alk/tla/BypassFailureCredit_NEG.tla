---- MODULE BypassFailureCredit_NEG ----
EXTENDS ALKConstructionTheoremWitness

AdvertisedBypassFailureResultHeld ==
    FailureGuaranteeBundleMatchesDerived(
        AdvertisedUnderFailure, DerivedNormalGuaranteeBundle,
        FALSE, TRUE, TRUE, TRUE, TRUE, TRUE, TRUE, TRUE)

ReachableBypassPathClassOf ==
    [claim \in Claims |->
        [action \in ActionLabels |->
            IF action = "external"
              THEN "bypass"
              ELSE PathClassOf[claim][action]]]

BypassTruthMismatchHeld ==
    ExactBypassFailureInputBinding(
        Claims, ActionLabels, PotentialActions,
        ClaimActions, ReachableBypassPathClassOf, TRUE)

BypassFailureResultHeld ==
    AdvertisedBypassFailureResultHeld \/ BypassTruthMismatchHeld

NegativeControlExpected == NegativeControlGate(BypassFailureResultHeld)

====
