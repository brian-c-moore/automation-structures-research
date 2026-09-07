---- MODULE RetainedRegistryNormalizationDrift_NEG ----
EXTENDS ALKSemanticModelWitness

DriftedNormalizedKeyOf ==
    [occurrence \in ObligationOccurrences |->
        IF occurrence = "Budget!SafetyInvariant"
          THEN "ResourceRegistry!UniqueMapping"
        ELSE NormalizedKeyOf[occurrence]]

RetainedConstructionRegistryBound ==
    RetainedConstructionBindingTyped(
        ObligationOccurrences, Structures, ExecutionModalities,
        StructureObligationOccurrences,
        ExecutionModalityObligationOccurrences,
        DriftedNormalizedKeyOf, ObligationPropertyClassOf,
        ProvedEquivalentOccurrences,
        RegistryObligationOccurrenceNames,
        RegistryEquivalentOccurrencePairs,
        RegistryCarrierObligationOccurrences,
        RegistryNormalizedKeyOf,
        RegistryObligationPropertyClassOf)

NegativeControlExpected == NegativeControlGate(RetainedConstructionRegistryBound)

====
