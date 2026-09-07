----------------- MODULE CompetitiveSelectionRankedDecomposed -----------------
(* Negative decomposition witness for CompetitiveSelectionRanked. Select is
   split into rank evaluation and commit; UpdateScores may replace the scores
   between those steps. CommitSelection can therefore publish a stale cached
   set that violates ThresholdOptimality or RankedTieBreak. *)
EXTENDS Naturals, FiniteSets

CONSTANTS Candidates, K, MaxScore

VARIABLES selected, scores, cached, pc

vars == <<selected, scores, cached, pc>>

WN == Cardinality(Candidates)
WEnum == CHOOSE seq \in [1..WN -> Candidates] :
             \A c \in Candidates : \E i \in 1..WN : seq[i] = c
Pos(c) == CHOOSE i \in 1..WN : WEnum[i] = c

TypeInvariant ==
    /\ selected \subseteq Candidates
    /\ scores \in [Candidates -> 0..MaxScore]

Better(c, d) ==
    \/ scores[c] > scores[d]
    \/ (scores[c] = scores[d] /\ Pos(c) < Pos(d))

Rank(c) == Cardinality({d \in Candidates : Better(d, c)})

BoundedMultiplicity ==
    Cardinality(selected) <= K

ThresholdOptimality ==
    \A s \in selected : \A c \in Candidates \ selected :
        scores[s] >= scores[c]

RankedTieBreak ==
    \A c \in selected : \A d \in Candidates \ selected : Better(c, d)

Init ==
    /\ selected = {}
    /\ scores \in [Candidates -> 0..MaxScore]
    /\ cached = {}
    /\ pc = "idle"

(* Evaluate ranks and retain the result without publishing it. *)
EvaluateRanks ==
    /\ pc = "idle"
    /\ cached' = {c \in Candidates : Rank(c) < K}
    /\ pc' = "ranked"
    /\ UNCHANGED <<selected, scores>>

(* Publish the retained result without re-evaluating the current scores. *)
CommitSelection ==
    /\ pc = "ranked"
    /\ selected' = cached
    /\ pc' = "idle"
    /\ UNCHANGED <<scores, cached>>

UpdateScores ==
    /\ \E new_scores \in [Candidates -> 0..MaxScore] :
        scores' = new_scores
    /\ selected' = {}
    /\ UNCHANGED <<cached, pc>>

Next == EvaluateRanks \/ CommitSelection \/ UpdateScores

Spec == Init /\ [][Next]_vars
=============================================================================
