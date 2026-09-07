---- MODULE CompetitiveSelectionRankedFromRegistry ----
\* Ranked selection over a ResourceRegistry score store.
\* Candidate order and top-K selection are derived projections; `taken` is the
\* only held glue variable and records whether selection has committed since
\* the last score update.
\*
\* BoundedMultiplicity, ThresholdOptimality, and RankedTieBreak follow from
\* the top-K projection, not from ResourceRegistry.UniqueMapping. The registry
\* supplies a unique score per candidate; the ranking and cutoff remain derived
\* structure owned by this construction.
\*
\* Multi-key score replacement is atomic. Separating score observation from the
\* ranked commit permits a cached order to become stale.

EXTENDS Naturals, FiniteSets

CONSTANTS Candidates, K, MaxScore

Scores == 0..MaxScore

\* ResourceRegistry entries plus a marker recording whether selection stands.
VARIABLES entries, taken

vars == <<entries, taken>>

\* The ResourceRegistry instance owns score-entry typing and uniqueness.
Registry == INSTANCE ResourceRegistry WITH Keys <- Candidates, Values <- Scores

RegistryUnique == Registry!UniqueMapping   \* every candidate maps to at most one score

\* Total score projection; an unregistered candidate has the minimum score 0.
ScoreOf(c) ==
    IF \E v \in Scores : <<c, v>> \in entries
    THEN CHOOSE v \in Scores : <<c, v>> \in entries
    ELSE 0

\* Target score vector projected from registry entries.
ScoreView == [c \in Candidates |-> ScoreOf(c)]

\* Candidate enumeration for the target's deterministic tie-break.
WN == Cardinality(Candidates)
WEnum == CHOOSE seq \in [1..WN -> Candidates] :
             \A c \in Candidates : \E i \in 1..WN : seq[i] = c
Pos(c) == CHOOSE i \in 1..WN : WEnum[i] = c

\* Derived score-then-position order and induced candidate rank.
BetterView(c, d) ==
    \/ ScoreOf(c) > ScoreOf(d)
    \/ (ScoreOf(c) = ScoreOf(d) /\ Pos(c) < Pos(d))

RankView(c) == Cardinality({d \in Candidates : BetterView(d, c)})

\* Top-K cut of the derived order.
TopK == {c \in Candidates : RankView(c) < K}

\* Target selected set. The marker decides only whether a selection stands,
\* never which candidates it holds: the target's
\* UpdateScores clears selected, so the target never exhibits a selected set that
\* is neither empty nor the current top-K, which is what makes this projection
\* faithful rather than an approximation.
SelectedView == IF taken THEN TopK ELSE {}

TypeInvariant ==
    /\ Registry!TypeInvariant
    /\ taken \in BOOLEAN

Init ==
    /\ entries = {}          \* Registry!Init verbatim
    /\ taken = FALSE

\* A single-candidate score write invokes Registry!Register and clears the
\* marker. It maps to UpdateScores, which admits any new score
\* vector and therefore admits one differing in a single candidate.
SetScore(c, v) ==
    /\ Registry!Register(c, v)
    /\ taken' = FALSE

\* Atomic whole-vector rewrite. This realizes one target UpdateScores step;
\* the single-key branch above invokes the registry operation directly.
SetScores(nv) ==
    /\ entries' = {<<c, nv[c]>> : c \in Candidates}
    /\ taken' = FALSE

\* Taking the selection writes only the marker: top-K is read from the
\* current scores through the projection, so there is no interval in which a
\* recorded order can go stale. Maps to the target's Select.
TakeSelection ==
    /\ taken' = TRUE
    /\ UNCHANGED entries

Next ==
    \/ \E c \in Candidates, v \in Scores : SetScore(c, v)
    \/ \E nv \in [Candidates -> Scores] : SetScores(nv)
    \/ TakeSelection

Spec == Init /\ [][Next]_vars

\* Target obligations restated over the construction state. The marker appears
\* explicitly because it determines whether SelectedView is empty or TopK.
MappedBoundedMultiplicity ==
    Cardinality(IF taken THEN TopK ELSE {}) <= K

MappedThresholdOptimality ==
    \A s \in (IF taken THEN TopK ELSE {}) :
        \A c \in Candidates \ (IF taken THEN TopK ELSE {}) :
            ScoreOf(s) >= ScoreOf(c)

MappedRankedTieBreak ==
    \A c \in (IF taken THEN TopK ELSE {}) :
        \A d \in Candidates \ (IF taken THEN TopK ELSE {}) :
            BetterView(c, d)

\* --- Refinement mapping to CompetitiveSelectionRanked ------------------------
\* Under scores <- ScoreView, CSR!Rank(c) is RankView(c) by substitution.
CSR == INSTANCE CompetitiveSelectionRanked WITH
        selected   <- SelectedView,
        scores     <- ScoreView,
        Candidates <- Candidates,
        K          <- K,
        MaxScore   <- MaxScore,
        CandidateOrder <- WEnum

\* Every construction behavior must map to a CompetitiveSelectionRanked behavior.
RankedRefinement == CSR!Spec

====
