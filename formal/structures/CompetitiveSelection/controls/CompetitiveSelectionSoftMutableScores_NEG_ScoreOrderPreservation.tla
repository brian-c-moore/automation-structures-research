---- MODULE CompetitiveSelectionSoftMutableScores_NEG_ScoreOrderPreservation ----
\* Negative control for ScoreOrderPreservation. UpdateScore changes a score
\* while retaining the prior apportionment, so the new score order can disagree
\* with the held weights. AssignNext and the mutable-score action surface are
\* otherwise unchanged.

EXTENDS CompetitiveSelectionSoft

UpdateScore(c, v) ==
    /\ scores' = [scores EXCEPT ![c] = v]
\* ---- MUTATION BEGINS -- to the closing marker, this replaces the base text.
    /\ UNCHANGED extra  \* MUTATED: the invalidated apportionment is left in place
\* ---- MUTATION ENDS.

MutableScoreNext ==
    \/ AssignNext
    \/ \E c \in Candidates, v \in 1..MaxScore : UpdateScore(c, v)

MutableScoreSpec == Init /\ [][MutableScoreNext]_vars

====
