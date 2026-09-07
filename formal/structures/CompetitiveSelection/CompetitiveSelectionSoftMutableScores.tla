---- MODULE CompetitiveSelectionSoftMutableScores ----
(* Soft competitive selection with environment-mutable scores.

   This module extends the immutable-score `CompetitiveSelectionSoft` carrier
   with one `UpdateScore` action and reuses its invariants, allocation action,
   and proof machinery. The stable name records that semantic distinction.

   `extra` is built incrementally
   under a fixed score vector: each award goes to the current Webster
   highest-priority candidate. A score change that left the partial
   apportionment in place would falsify ScoreOrderPreservation and
   TieBoundedness even with atomic execution. A score update therefore resets
   `extra` to the reserved floor before allocation resumes. The paired
   decomposed control separates score observation from award commit and makes
   the stale-score race reachable.                                        *)
EXTENDS CompetitiveSelectionSoft

\* The environment's score writer. The new score stays in
\* the spec's own score domain -- Init draws from 1..MaxScore and the base
\* proof carries ScorePositive because PriorityTie needs a positive score to
\* cancel a common factor. Under a live writer that fact survives because the
\* writer preserves it, where in the base module it survived because
\* nothing wrote scores at all.
UpdateScore(c, v) ==
    /\ scores' = [scores EXCEPT ![c] = v]
    /\ extra'  = [d \in Candidates |-> 0]

MutableScoreNext ==
    \/ AssignNext
    \/ \E c \in Candidates, v \in 1..MaxScore : UpdateScore(c, v)

MutableScoreSpec == Init /\ [][MutableScoreNext]_vars

\* MutableScoreSpec => [](TypeInvariant /\ NonNegativity /\ BoundedTotal /\
\* Normalization /\ UniversalContribution /\ ScoreOrderPreservation /\
\* TieBoundedness) is proved in CompetitiveSelectionSoftMutableScores_Proof.tla.
====
