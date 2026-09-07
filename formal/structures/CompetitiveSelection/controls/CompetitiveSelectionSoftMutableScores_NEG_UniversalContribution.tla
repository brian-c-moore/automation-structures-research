---- MODULE CompetitiveSelectionSoftMutableScores_NEG_UniversalContribution ----
\* Negative control for UniversalContribution. UpdateScore sets every extra
\* allocation to -1, so each derived weight is zero. The mutable-score action
\* surface is otherwise unchanged.

EXTENDS CompetitiveSelectionSoft

UpdateScore(c, v) ==
    /\ scores' = [scores EXCEPT ![c] = v]
\* ---- MUTATION BEGINS -- to the closing marker, this replaces the base text.
    /\ extra'  = [d \in Candidates |-> 0 - 1]
\* ---- MUTATION ENDS.

MutableScoreNext ==
    \/ AssignNext
    \/ \E c \in Candidates, v \in 1..MaxScore : UpdateScore(c, v)

MutableScoreSpec == Init /\ [][MutableScoreNext]_vars

====
