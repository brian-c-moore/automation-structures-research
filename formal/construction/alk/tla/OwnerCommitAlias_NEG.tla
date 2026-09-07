---- MODULE OwnerCommitAlias_NEG ----
EXTENDS ALKSemanticModelWitness

OwnerAliasLeft == "Budget!SafetyInvariant"
OwnerAliasRight == "Sequential!HistoryPositionAgreement"

OwnerAliasedNormalizedKeyOf ==
    [occurrence \in ObligationOccurrences |->
        IF occurrence \in {OwnerAliasLeft, OwnerAliasRight}
          THEN OwnerAliasLeft
        ELSE NormalizedKeyOf[occurrence]]

OwnerAliasedPredicateOf ==
    [occurrence \in ObligationOccurrences |->
        IF occurrence \in {OwnerAliasLeft, OwnerAliasRight}
          THEN PredicateOf[OwnerAliasLeft]
        ELSE PredicateOf[occurrence]]

OwnerAliasedObligations ==
    NormalizedObligations(
        ObligationOccurrences, OwnerAliasedNormalizedKeyOf)
OwnerAliasedObligationPropertyClass ==
    [obligation \in OwnerAliasedObligations |->
        ObligationPropertyClass[obligation]]
OwnerAliasProofs ==
    {<<OwnerAliasLeft, OwnerAliasRight>>,
     <<OwnerAliasRight, OwnerAliasLeft>>}

OwnerCommitNormalizationFor(owners, commits) ==
    ObligationNormalizationTyped(
        ObligationOccurrences, OwnerAliasedObligations,
        PredicateIds, ScopeIds, ObservationBoundaryIds,
        FailureCeilingIds, PropertyClassesUsed,
        Actors, CommitBoundaryIds,
        OwnerAliasedNormalizedKeyOf, OwnerAliasedPredicateOf, ScopeOf,
        ObligationObservationBoundaryOf, ObligationFailureCeilingOf,
        ObligationPropertyClassOf, OwnerAliasedObligationPropertyClass,
        owners, commits, OwnerAliasProofs)

\* The adjacent interface fixture supplies matching owner/commit values.
\* It does not prove equivalence of the actual Budget and Sequential predicates.
OwnerAliasAlignedOwners ==
    [occurrence \in ObligationOccurrences |->
        IF occurrence \in {OwnerAliasLeft, OwnerAliasRight}
          THEN OccurrenceOwner[OwnerAliasLeft]
        ELSE OccurrenceOwner[occurrence]]
OwnerAliasAlignedCommits ==
    [occurrence \in ObligationOccurrences |->
        IF occurrence \in {OwnerAliasLeft, OwnerAliasRight}
          THEN OccurrenceCommitBoundary[OwnerAliasLeft]
        ELSE OccurrenceCommitBoundary[occurrence]]
OwnerAliasFixtureHeld ==
    /\ ModelBoundaryHolds
    /\ OwnerCommitNormalizationFor(
           OwnerAliasAlignedOwners, OwnerAliasAlignedCommits)

OwnerCommitNormalizationHeld ==
    OwnerCommitNormalizationFor(OccurrenceOwner, OccurrenceCommitBoundary)
NegativeControlExpected == NegativeControlGate(OwnerCommitNormalizationHeld)

====
