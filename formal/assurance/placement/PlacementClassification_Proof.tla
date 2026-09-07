---- MODULE PlacementClassification_Proof ----
EXTENDS PlacementClassification, TLAPS

ASSUME PlacementsDistinct == Direct /= Delegated
ASSUME TimingsDistinct ==
    /\ NoAssurance /= PreCommit
    /\ PreCommit /= AtCommit
    /\ AtCommit /= PostCommit
    /\ NoAssurance /= AtCommit
    /\ NoAssurance /= PostCommit
    /\ PreCommit /= PostCommit
ASSUME KindsDistinct ==
    /\ Prevention /= Detection
    /\ Detection /= Recovery
    /\ Recovery /= Lost
    /\ Prevention /= Recovery
    /\ Prevention /= Lost
    /\ Detection /= Lost

THEOREM ClassificationRange ==
    (\A p \in Placements,
        t \in Timings,
        healthy \in BOOLEAN,
        partitioned \in BOOLEAN,
        recoveryCapable \in BOOLEAN:
        EffectiveKind(p, t, healthy, partitioned, recoveryCapable) \in Kinds)
BY SMT DEF EffectiveKind, Prevents, Placements, Timings, Kinds

THEOREM PostCommitIsNotPrevention ==
    (\A healthy \in BOOLEAN,
        partitioned \in BOOLEAN,
        recoveryCapable \in BOOLEAN:
        EffectiveKind(Delegated, PostCommit, healthy, partitioned, recoveryCapable)
        /= Prevention)
BY SMT, PlacementsDistinct, TimingsDistinct, KindsDistinct
   DEF EffectiveKind, Prevents

THEOREM UnavailableAssuranceLoses ==
    (\A t \in Timings, recoveryCapable \in BOOLEAN:
        /\ EffectiveKind(Delegated, t, FALSE, FALSE, recoveryCapable) = Lost
        /\ EffectiveKind(Delegated, t, TRUE, TRUE, recoveryCapable) = Lost)
BY SMT, PlacementsDistinct DEF EffectiveKind, Prevents, Timings

THEOREM PreventionHasCommitControl ==
    (\A p \in Placements,
        t \in Timings,
        healthy \in BOOLEAN,
        partitioned \in BOOLEAN,
        recoveryCapable \in BOOLEAN:
        EffectiveKind(p, t, healthy, partitioned, recoveryCapable) = Prevention
        => (p = Direct \/ (t \in {PreCommit, AtCommit} /\ healthy /\ ~partitioned)))
BY SMT, PlacementsDistinct, KindsDistinct
   DEF EffectiveKind, Prevents, Placements, Timings

====
