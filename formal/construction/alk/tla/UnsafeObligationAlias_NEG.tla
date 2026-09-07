---- MODULE UnsafeObligationAlias_NEG ----
EXTENDS ALKSemanticModelWitness

AliasLeft == "Budget!SafetyInvariant"
AliasRight == "ResourceRegistry!UniqueMapping"

UnsafeNormalizedKeyOf ==
    [occurrence \in ObligationOccurrences |->
        IF occurrence \in {AliasLeft, AliasRight}
          THEN "unsafe-cross-requirement-alias"
        ELSE NormalizedKeyOf[occurrence]]
UnsafePredicateOf ==
    [occurrence \in ObligationOccurrences |->
        IF occurrence \in {AliasLeft, AliasRight}
          THEN PredicateOf[AliasLeft]
        ELSE PredicateOf[occurrence]]

UnsafeObligations ==
    NormalizedObligations(ObligationOccurrences, UnsafeNormalizedKeyOf)
UnsafeObligationPropertyClass ==
    [obligation \in UnsafeObligations |->
        IF obligation = "unsafe-cross-requirement-alias"
          THEN "safety"
        ELSE ObligationPropertyClass[obligation]]

SemanticNormalizationFor(equivalencePairs) ==
    ObligationNormalizationTyped(
        ObligationOccurrences, UnsafeObligations,
        PredicateIds, ScopeIds, ObservationBoundaryIds,
        FailureCeilingIds, PropertyClassesUsed,
        Actors, CommitBoundaryIds,
        UnsafeNormalizedKeyOf, UnsafePredicateOf, ScopeOf,
        ObligationObservationBoundaryOf, ObligationFailureCeilingOf,
        ObligationPropertyClassOf, UnsafeObligationPropertyClass,
        OccurrenceOwner,
        OccurrenceCommitBoundary, equivalencePairs)

\* This fixture supplies an alleged equivalence to isolate its omission.
\* It does not prove equivalence of the actual carrier predicates.
UnsafeAliasFixtureHeld ==
    /\ ModelBoundaryHolds
    /\ SemanticNormalizationFor(
           {<<AliasLeft, AliasRight>>, <<AliasRight, AliasLeft>>})
SemanticNormalizationHeld == SemanticNormalizationFor({})
NegativeControlExpected == NegativeControlGate(SemanticNormalizationHeld)

====
