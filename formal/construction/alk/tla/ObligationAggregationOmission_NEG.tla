---- MODULE ObligationAggregationOmission_NEG ----
EXTENDS ALKSemanticModelWitness

OmittedClaimObligations ==
    [claim \in Claims |->
        ClaimObligations[claim] \ {"Budget!SafetyInvariant"}]

ExactObligationAggregation ==
    ALKConstructionSelectionTyped(
        Claims, Structures, ExecutionModalities,
        ObligationOccurrences, Obligations,
        StructureObligationOccurrences,
        ExecutionModalityObligationOccurrences,
        NormalizedKeyOf,
        SelectedStructures, SelectedExecutionModality,
        CompositionSeamObligationOccurrences,
        ClaimObligationOccurrences, OmittedClaimObligations)

NegativeControlExpected == NegativeControlGate(ExactObligationAggregation)

====
