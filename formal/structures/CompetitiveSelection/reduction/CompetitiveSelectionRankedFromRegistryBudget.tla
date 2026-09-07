---- MODULE CompetitiveSelectionRankedFromRegistryBudget ----
\* Ranked selection over ResourceRegistry and Budget. The
\* seat bound is Budget capacity K, and the selection cut is Budget's allocated
\* count rather than the literal K:
\*     SelectedView == {c \in Candidates : RankView(c) < allocated}
\* Injective rank gives Cardinality(selected) <= allocated, while Budget's
\* SafetyInvariant supplies allocated <= capacity = K. The construction adds no
\* separate selection-count guard.
\*
\* All held state belongs to the registry or Budget components; the remaining
\* target views are projections.
\*
\* Budget supplies only the seat ceiling. ThresholdOptimality and RankedTieBreak
\* arise from the score/rank projections and are not Budget guarantees.
\*
\* The mapping assumes atomic multi-key score rewrites and an atomic fused
\* registry-plus-Budget selection commit.

EXTENDS Naturals, FiniteSets

CONSTANTS Candidates, K, MaxScore

Scores == 0..MaxScore

\* Registry entries and Budget state are the complete held state.
VARIABLES entries, capacity, allocated, reserved, pending_eviction

vars == <<entries, capacity, allocated, reserved, pending_eviction>>

Registry == INSTANCE ResourceRegistry WITH Keys <- Candidates, Values <- Scores
Seats    == INSTANCE Budget WITH Capacity <- K

RegistryUnique == Registry!UniqueMapping
SeatCeiling    == Seats!SafetyInvariant   \* allocated + reserved + pending <= capacity

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

\* The selection cut is Budget's allocated seat count.
SelectedView == {c \in Candidates : RankView(c) < allocated}

TypeInvariant ==
    /\ Registry!TypeInvariant
    /\ Seats!TypeInvariant

Init ==
    /\ entries = {}      \* Registry!Init verbatim
    /\ Seats!Init        \* capacity = K, allocated = reserved = pending = 0

\* Releasing every held seat. For allocated > 0 this is Seats!Release(allocated)
\* -- the component's own operation, whose guard `amount <= allocated` holds by
\* construction; for allocated = 0 it is a stutter on Budget's state, which
\* Release's own quantifier (a \in 1..allocated) excludes rather than performs.
ClearSeats ==
    /\ allocated' = 0
    /\ UNCHANGED <<capacity, reserved, pending_eviction>>

SetScore(c, v) ==
    /\ Registry!Register(c, v)
    /\ ClearSeats

SetScores(nv) ==
    /\ entries' = {<<c, nv[c]>> : c \in Candidates}
    /\ ClearSeats

\* Selection atomically charges K Budget seats. Top-K is derived from current
\* scores in the same step, so no cached-order interval exists.
TakeSelection ==
    /\ Seats!TryAllocate(K)
    /\ UNCHANGED entries

Next ==
    \/ \E c \in Candidates, v \in Scores : SetScore(c, v)
    \/ \E nv \in [Candidates -> Scores] : SetScores(nv)
    \/ TakeSelection

Spec == Init /\ [][Next]_vars

\* Target obligations restated over registry and Budget state.
MappedBoundedMultiplicity ==
    Cardinality({c \in Candidates : RankView(c) < allocated}) <= K

MappedThresholdOptimality ==
    \A s \in SelectedView : \A c \in Candidates \ SelectedView :
        ScoreOf(s) >= ScoreOf(c)

MappedRankedTieBreak ==
    \A c \in SelectedView : \A d \in Candidates \ SelectedView :
        BetterView(c, d)

\* --- Refinement mapping to CompetitiveSelectionRanked ------------------------
CSR == INSTANCE CompetitiveSelectionRanked WITH
        selected   <- SelectedView,
        scores     <- ScoreView,
        Candidates <- Candidates,
        K          <- K,
        MaxScore   <- MaxScore,
        CandidateOrder <- WEnum

RankedRefinement == CSR!Spec
====
