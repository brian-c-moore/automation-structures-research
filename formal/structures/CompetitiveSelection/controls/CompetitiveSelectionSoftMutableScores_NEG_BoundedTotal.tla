---- MODULE CompetitiveSelectionSoftMutableScores_NEG_BoundedTotal ----
\* Negative control for BoundedTotal. UpdateScore assigns WeightTotal extra
\* units to every candidate, so the derived weight sum exceeds WeightTotal.
\* The mutable-score action surface is otherwise unchanged.

EXTENDS CompetitiveSelectionSoft

UpdateScore(c, v) ==
    /\ scores' = [scores EXCEPT ![c] = v]
\* ---- MUTATION BEGINS -- to the closing marker, this replaces the base text.
    /\ extra'  = [d \in Candidates |-> WeightTotal]
\* ---- MUTATION ENDS.

MutableScoreNext ==
    \/ AssignNext
    \/ \E c \in Candidates, v \in 1..MaxScore : UpdateScore(c, v)

MutableScoreSpec == Init /\ [][MutableScoreNext]_vars

====
