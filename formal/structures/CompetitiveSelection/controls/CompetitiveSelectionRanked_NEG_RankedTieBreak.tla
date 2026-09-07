---- MODULE CompetitiveSelectionRanked_NEG_RankedTieBreak ----
\* Negative control for RankedTieBreak. Select may choose any score-threshold-
\* optimal K-subset, so an exact cutoff tie need not follow the deterministic
\* candidate-position order.

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

\* ---- MUTATION BEGINS -- to the closing marker, this replaces the base text.
Select ==
    /\ \E S \in SUBSET Candidates :
        /\ Cardinality(S) = K
        /\ \A c \in S : \A d \in Candidates \ S : scores[c] >= scores[d]
        /\ selected' = S  \* MUTATED: any threshold-optimal subset, not the deterministic top-K
    /\ UNCHANGED scores
\* ---- MUTATION ENDS.

UpdateScores ==
    /\ \E new_scores \in [Candidates -> 0..MaxScore] :
        scores' = new_scores
    /\ selected' = {}

Next == Select \/ UpdateScores

Spec == Init /\ [][Next]_vars

====
