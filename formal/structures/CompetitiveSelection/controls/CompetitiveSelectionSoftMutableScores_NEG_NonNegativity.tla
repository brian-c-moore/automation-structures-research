---- MODULE CompetitiveSelectionSoftMutableScores_NEG_NonNegativity ----
\* Negative control for NonNegativity. UpdateScore sets every extra allocation
\* to -2, so each derived weight is -1. The mutable-score action surface is
\* otherwise unchanged.

EXTENDS CompetitiveSelectionSoft

UpdateScore(c, v) ==
    /\ scores' = [scores EXCEPT ![c] = v]
\* ---- MUTATION BEGINS -- to the closing marker, this replaces the base text.
    /\ extra'  = [d \in Candidates |-> 0 - 2]
\* ---- MUTATION ENDS.

MutableScoreNext ==
    \/ AssignNext
    \/ \E c \in Candidates, v \in 1..MaxScore : UpdateScore(c, v)

MutableScoreSpec == Init /\ [][MutableScoreNext]_vars

====
