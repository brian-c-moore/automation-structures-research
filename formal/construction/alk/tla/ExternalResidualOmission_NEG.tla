---- MODULE ExternalResidualOmission_NEG ----
EXTENDS ALKSemanticModelWitness

OmittedResidualActions ==
    [claim \in Claims |->
        ResidualActions[claim] \ {"external-store"}]

ExternalResidualInventoryCoherent ==
    ALKClaimBoundaryCoherent(
        Claims, ClaimActions, AdmittedActions,
        ObligationRelevantActions, ExternalActions,
        CommitActions, FailureActions, OmittedResidualActions)

NegativeControlExpected == NegativeControlGate(ExternalResidualInventoryCoherent)

====
