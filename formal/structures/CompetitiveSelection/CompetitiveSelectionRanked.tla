---- MODULE CompetitiveSelectionRanked ----
EXTENDS Naturals, FiniteSets

CONSTANTS Candidates, K, MaxScore, CandidateOrder

\* Composite values stay in TLA+ and the bounded TLC configurations bind the
\* constant by definition substitution.
ConfiguredCandidateOrder == <<"c1", "c2", "c3", "c4">>

VARIABLES selected, scores

vars == <<selected, scores>>

\* Explicit candidate enumeration for deterministic lowest-position
\* tie-breaking. A refinement must bind it to the implementation order.
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

\* The score-then-position strict total order: c is "better" than d if it scores
\* strictly higher, or ties on score but has the lower enumeration position.  Pos
\* is a bijection, so every exact tie is resolved and Better is a strict total
\* order (irreflexive, trichotomous, transitive -- proved in the _Proof module).
Better(c, d) ==
    \/ scores[c] > scores[d]
    \/ (scores[c] = scores[d] /\ Pos(c) < Pos(d))

\* Rank(c): the number of candidates strictly Better than c.  Because Better is a
\* strict total order over the finite Candidates, Rank is injective (a bijection
\* onto 0..(WN-1)); the unique best candidate has Rank 0.
Rank(c) == Cardinality({d \in Candidates : Better(d, c)})

\* Select exports the same exact-count and score-then-position ordering relation
\* as the executable contract. The proof module shows that this relation has the
\* unique Rank-below-K solution. UpdateScores atomically clears selected, making
\* the three selection obligations vacuous until Select re-establishes them.

\* Bounded multiplicity: at most K winners
BoundedMultiplicity ==
    Cardinality(selected) <= K

\* Threshold optimality: every selected candidate scores at least as high
\* as every non-selected candidate
ThresholdOptimality ==
    \A s \in selected : \A c \in Candidates \ selected :
        scores[s] >= scores[c]

\* Tie-break: every selected candidate is Better than every non-selected one.
\* With top-K-by-Rank selection this pins selected to the unique deterministic
\* top K under score-then-position order.
RankedTieBreak ==
    \A c \in selected : \A d \in Candidates \ selected : Better(c, d)

Init ==
    /\ selected = {}
    /\ scores \in [Candidates -> 0..MaxScore]

\* Select the deterministic top-K through the exported contract relation:
\* exactly K candidates, each Better than every unselected candidate, with
\* scores unchanged. ContractSelectStep proves that the only such set is the
\* Rank-below-K set, so no subset choice remains at a cutoff tie.
Select ==
    /\ selected' \subseteq Candidates
    /\ Cardinality(selected') = K
    /\ \A c \in selected' : \A d \in Candidates \ selected' : Better(c, d)
    /\ UNCHANGED scores

UpdateScores ==
    /\ \E new_scores \in [Candidates -> 0..MaxScore] :
        scores' = new_scores
    /\ selected' = {}

Next == Select \/ UpdateScores

Spec == Init /\ [][Next]_vars

\* Spec => [](BoundedMultiplicity /\ ThresholdOptimality /\ RankedTieBreak): proved
\* as the conjunction of BoundedMultiplicitySafety, ThresholdOptimalitySafety,
\* RankedTieBreakSafety in CompetitiveSelectionRanked_Proof.tla.
====
