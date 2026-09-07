---- MODULE CompetitiveSelectionRankedFromRegistry_NEG ----
\* Refinement control for CompetitiveSelectionRankedFromRegistry. Candidate
\* rank is cached by SnapshotOrder and later consumed by TakeSelection. A score
\* write between those actions makes SelectedView use an order derived from old
\* scores. The resulting nonempty stale top-K is neither a target Select under
\* current scores, a target UpdateScores step, nor a stutter; RankedRefinement
\* must fail. Registry actions and uniqueness are otherwise unchanged.

EXTENDS Naturals, FiniteSets

CONSTANTS Candidates, K, MaxScore

Scores == 0..MaxScore

VARIABLES entries, taken, snapRank

vars == <<entries, taken, snapRank>>

Registry == INSTANCE ResourceRegistry WITH Keys <- Candidates, Values <- Scores

RegistryUnique == Registry!UniqueMapping

ScoreOf(c) ==
    IF \E v \in Scores : <<c, v>> \in entries
    THEN CHOOSE v \in Scores : <<c, v>> \in entries
    ELSE 0

ScoreView == [c \in Candidates |-> ScoreOf(c)]

WN == Cardinality(Candidates)
WEnum == CHOOSE seq \in [1..WN -> Candidates] :
             \A c \in Candidates : \E i \in 1..WN : seq[i] = c
Pos(c) == CHOOSE i \in 1..WN : WEnum[i] = c

BetterView(c, d) ==
    \/ ScoreOf(c) > ScoreOf(d)
    \/ (ScoreOf(c) = ScoreOf(d) /\ Pos(c) < Pos(d))

RankView(c) == Cardinality({d \in Candidates : BetterView(d, c)})

\* Fault: top-K is cut from cached rank rather than current scores.
SelectedView == IF taken THEN {c \in Candidates : snapRank[c] < K} ELSE {}

TypeInvariant ==
    /\ Registry!TypeInvariant
    /\ taken \in BOOLEAN
    /\ snapRank \in [Candidates -> 0..WN]

\* The initial snapshot matches the initial scores; only later staleness faults.
Init ==
    /\ entries = {}
    /\ taken = FALSE
    /\ snapRank = [c \in Candidates |-> RankView(c)]

SetScore(c, v) ==
    /\ Registry!Register(c, v)
    /\ taken' = FALSE
    /\ UNCHANGED snapRank

SetScores(nv) ==
    /\ entries' = {<<c, nv[c]>> : c \in Candidates}
    /\ taken' = FALSE
    /\ UNCHANGED snapRank

\* Cache the rank induced by current scores.
SnapshotOrder ==
    /\ snapRank' = [c \in Candidates |-> RankView(c)]
    /\ UNCHANGED <<entries, taken>>

\* Commit selection from the cached order.
TakeSelection ==
    /\ taken' = TRUE
    /\ UNCHANGED <<entries, snapRank>>

Next ==
    \/ \E c \in Candidates, v \in Scores : SetScore(c, v)
    \/ \E nv \in [Candidates -> Scores] : SetScores(nv)
    \/ SnapshotOrder
    \/ TakeSelection

Spec == Init /\ [][Next]_vars

CSR == INSTANCE CompetitiveSelectionRanked WITH
        selected   <- SelectedView,
        scores     <- ScoreView,
        Candidates <- Candidates,
        K          <- K,
        MaxScore   <- MaxScore,
        CandidateOrder <- WEnum

RankedRefinement == CSR!Spec
====
