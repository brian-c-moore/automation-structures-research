---- MODULE RetainedPropertyClassDrift_NEG ----
EXTENDS ALKSemanticModelWitness

DriftedPropertyClassOf ==
    [occurrence \in ObligationOccurrences |->
        IF occurrence =
             "PropagationPass!EventualSettledOrIterationLimit"
          THEN "safety"
        ELSE ObligationPropertyClassOf[occurrence]]

RetainedPropertyClassesBound ==
    RetainedConstructionBindingTyped(
        ObligationOccurrences, Structures, ExecutionModalities,
        StructureObligationOccurrences,
        ExecutionModalityObligationOccurrences,
        NormalizedKeyOf, DriftedPropertyClassOf,
        ProvedEquivalentOccurrences,
        RegistryObligationOccurrenceNames,
        RegistryEquivalentOccurrencePairs,
        RegistryCarrierObligationOccurrences,
        RegistryNormalizedKeyOf,
        RegistryObligationPropertyClassOf)

NegativeControlExpected == NegativeControlGate(RetainedPropertyClassesBound)

====
