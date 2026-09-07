---- MODULE PlacementClassification ----
EXTENDS Naturals

CONSTANTS Direct, Delegated,
          NoAssurance, PreCommit, AtCommit, PostCommit,
          Prevention, Detection, Recovery, Lost

Placements == {Direct, Delegated}
Timings == {NoAssurance, PreCommit, AtCommit, PostCommit}
Kinds == {Prevention, Detection, Recovery, Lost}

Prevents(p, t, healthy, partitioned) ==
    p = Direct
    \/ /\ p = Delegated
       /\ t \in {PreCommit, AtCommit}
       /\ healthy
       /\ ~partitioned

EffectiveKind(p, t, healthy, partitioned, recoveryCapable) ==
    IF Prevents(p, t, healthy, partitioned) THEN Prevention
    ELSE IF /\ p = Delegated
            /\ t = PostCommit
            /\ healthy
            /\ ~partitioned
            /\ recoveryCapable
         THEN Recovery
    ELSE IF /\ p = Delegated
            /\ t = PostCommit
            /\ healthy
            /\ ~partitioned
         THEN Detection
    ELSE Lost

====
