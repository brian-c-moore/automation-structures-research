---- MODULE CompetitiveSelectionRanked_NEG_BoundedMultiplicity ----
\* Negative control for BoundedMultiplicity. Select uses Rank < K + 1 and can
\* commit one candidate beyond the configured top-K ceiling. Score ordering and
\* the remaining transition relation match the carrier.

EXTENDS Naturals, FiniteSets

CONSTANTS Candidates, K, MaxScore, CandidateOrder

ConfiguredCandidateOrder == <<"c1", "c2", "c3", "c4">>

VARIABLES selected, scores

vars == <<selected, scores>>

WN == Cardinality(Candidates)
ASSUME CandidateOrderType ==
    /\ CandidateOrder \in [1..WN -> Candidates]
    /\ \A c \in Candidates : \E i \in 1..WN : CandidateOrder[i] = c
    /\ \A i, j \in 1..WN : CandidateOrder[i] = CandidateOrder[j] => i = j
ASSUME KType == K \in 1..WN
WEnum == CandidateOrder
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

Select ==
\* ---- MUTATION BEGINS -- to the closing marker, this replaces the base text.
    /\ selected' = {c \in Candidates : Rank(c) < K + 1}  \* MUTATED: one seat too many
\* ---- MUTATION ENDS.
    /\ UNCHANGED scores

UpdateScores ==
    /\ \E new_scores \in [Candidates -> 0..MaxScore] :
        scores' = new_scores
    /\ selected' = {}

Next == Select \/ UpdateScores

Spec == Init /\ [][Next]_vars

====
