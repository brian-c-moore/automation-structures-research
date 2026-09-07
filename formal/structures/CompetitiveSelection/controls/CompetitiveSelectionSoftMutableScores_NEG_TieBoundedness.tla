---- MODULE CompetitiveSelectionSoftMutableScores_NEG_TieBoundedness ----
\* Negative control for TieBoundedness. UpdateScore changes a score while
\* retaining the previous apportionment, allowing newly tied candidates to
\* differ by more than one weight unit.

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
