---- MODULE CompetitiveSelectionImplRefinesSpec ----
(***************************************************************************)
(* Four contract transcriptions share this package: hard-exclusive,        *)
(* reserved-floor soft, mutable-score soft, and ranked top-K. Vec fields   *)
(* map indexwise to functions or sets. Fixed finite score ceilings are      *)
(* explicit profile premises. No probability or real-softmax claim is made. *)
(***************************************************************************)
\* EXPECT: OK
EXTENDS Naturals, FiniteSets

CONSTANTS NumSeats, NumCandidates, MaxScore, WeightTotal, K, NullValue
ASSUME SeatType == NumSeats \in Nat /\ NumSeats >= 2
ASSUME CandidateType == NumCandidates \in Nat /\ NumCandidates >= 2
ASSUME ScoreType == MaxScore \in Nat /\ MaxScore >= 1
ASSUME WeightType == WeightTotal \in Nat /\ WeightTotal >= NumCandidates
ASSUME KType == K \in 1..NumCandidates

Seats == 0..(NumSeats - 1)
Candidates == 0..(NumCandidates - 1)
CandidateOrder == [i \in 1..NumCandidates |-> i - 1]

VARIABLES hard_num_seats, hard_num_candidates, hard_max_score,
          hard_allocation, hard_scores,
          soft_weight_total, soft_max_score, soft_scores, soft_extra,
          mutable_weight_total, mutable_max_score, mutable_scores, mutable_extra,
          ranked_k, ranked_max_score, ranked_selected, ranked_scores

hard_vars == <<hard_num_seats, hard_num_candidates, hard_max_score,
               hard_allocation, hard_scores>>
soft_vars == <<soft_weight_total, soft_max_score, soft_scores, soft_extra>>
mutable_vars == <<mutable_weight_total, mutable_max_score,
                  mutable_scores, mutable_extra>>
ranked_vars == <<ranked_k, ranked_max_score, ranked_selected, ranked_scores>>
vars == <<hard_num_seats, hard_num_candidates, hard_max_score,
          hard_allocation, hard_scores,
          soft_weight_total, soft_max_score, soft_scores, soft_extra,
          mutable_weight_total, mutable_max_score, mutable_scores, mutable_extra,
          ranked_k, ranked_max_score, ranked_selected, ranked_scores>>

H == INSTANCE CompetitiveSelectionHardExclusive WITH
        Seats <- Seats,
        Candidates <- Candidates,
        MaxScore <- MaxScore,
        NULL <- NullValue,
        CandidateOrder <- CandidateOrder,
        allocation <- hard_allocation,
        scores <- hard_scores
S == INSTANCE CompetitiveSelectionSoft WITH
        Candidates <- Candidates,
        WeightTotal <- WeightTotal,
        MaxScore <- MaxScore,
        CandidateOrder <- CandidateOrder,
        scores <- soft_scores,
        extra <- soft_extra
MS == INSTANCE CompetitiveSelectionSoftMutableScores WITH
        Candidates <- Candidates,
        WeightTotal <- WeightTotal,
        MaxScore <- MaxScore,
        CandidateOrder <- CandidateOrder,
        scores <- mutable_scores,
        extra <- mutable_extra
R == INSTANCE CompetitiveSelectionRanked WITH
        Candidates <- Candidates,
        K <- K,
        MaxScore <- MaxScore,
        CandidateOrder <- CandidateOrder,
        selected <- ranked_selected,
        scores <- ranked_scores

HardBest(seat) == CHOOSE c \in H!Available(seat) :
    /\ \A other \in H!Available(seat) :
          hard_scores[seat][other] <= hard_scores[seat][c]
    /\ \A other \in H!Available(seat) :
          hard_scores[seat][other] = hard_scores[seat][c]
              => H!Pos(c) <= H!Pos(other)

HardInvariant ==
    /\ hard_num_seats = NumSeats
    /\ hard_num_candidates = NumCandidates
    /\ hard_max_score = MaxScore
    /\ H!TypeInvariant /\ H!MutualExclusion
        /\ H!WinnerOptimality /\ H!WinnerTieBreak
SoftInvariant ==
    /\ soft_weight_total = WeightTotal
    /\ soft_max_score = MaxScore
    /\ S!TypeInvariant /\ S!NonNegativity /\ S!BoundedTotal
        /\ S!Normalization /\ S!UniversalContribution
        /\ S!ScoreOrderPreservation /\ S!TieBoundedness
MutableInvariant ==
    /\ mutable_weight_total = WeightTotal
    /\ mutable_max_score = MaxScore
    /\ MS!TypeInvariant /\ MS!NonNegativity /\ MS!BoundedTotal
        /\ MS!Normalization /\ MS!UniversalContribution
        /\ MS!ScoreOrderPreservation /\ MS!TieBoundedness
RankedInvariant ==
    /\ ranked_k = K
    /\ ranked_max_score = MaxScore
    /\ R!TypeInvariant /\ R!BoundedMultiplicity
        /\ R!ThresholdOptimality /\ R!RankedTieBreak
ImplInvariant ==
    HardInvariant /\ SoftInvariant /\ MutableInvariant /\ RankedInvariant

Init ==
    /\ hard_num_seats = NumSeats
    /\ hard_num_candidates = NumCandidates
    /\ hard_max_score = MaxScore
    /\ hard_allocation = [s \in Seats |-> NullValue]
    /\ hard_scores = [s \in Seats |-> [c \in Candidates |-> 0]]
    /\ soft_weight_total = WeightTotal
    /\ soft_max_score = MaxScore
    /\ soft_scores \in [Candidates -> 1..MaxScore]
    /\ soft_extra = [c \in Candidates |-> 0]
    /\ mutable_weight_total = WeightTotal
    /\ mutable_max_score = MaxScore
    /\ mutable_scores \in [Candidates -> 1..MaxScore]
    /\ mutable_extra = [c \in Candidates |-> 0]
    /\ ranked_k = K
    /\ ranked_max_score = MaxScore
    /\ ranked_selected = {}
    /\ ranked_scores \in [Candidates -> 0..MaxScore]
    /\ ImplInvariant

ImplHardEvaluate(seat) ==
    /\ HardInvariant
    /\ seat \in Seats
    /\ hard_allocation[seat] = NullValue
    /\ H!Available(seat) /= {}
    /\ hard_allocation' = [hard_allocation EXCEPT ![seat] = HardBest(seat)]
    /\ hard_scores' = hard_scores
    /\ UNCHANGED <<hard_num_seats, hard_num_candidates, hard_max_score>>
    /\ HardInvariant'

ImplHardUpdateScore(seat, candidate, value) ==
    /\ HardInvariant
    /\ seat \in Seats
    /\ candidate \in Candidates
    /\ value \in 0..MaxScore
    /\ hard_scores' = [hard_scores EXCEPT ![seat][candidate] = value]
    /\ hard_allocation' = [s \in Seats |-> NullValue]
    /\ UNCHANGED <<hard_num_seats, hard_num_candidates, hard_max_score>>
    /\ HardInvariant'

ImplSoftAssign ==
    /\ SoftInvariant
    /\ S!WSum[S!WN] < WeightTotal
    /\ soft_extra' = [soft_extra EXCEPT ![S!Winner] = @ + 1]
    /\ soft_scores' = soft_scores
    /\ UNCHANGED <<soft_weight_total, soft_max_score>>
    /\ SoftInvariant'

ImplMutableAssign ==
    /\ MutableInvariant
    /\ MS!WSum[MS!WN] < WeightTotal
    /\ mutable_extra' = [mutable_extra EXCEPT ![MS!Winner] = @ + 1]
    /\ mutable_scores' = mutable_scores
    /\ UNCHANGED <<mutable_weight_total, mutable_max_score>>
    /\ MutableInvariant'

ImplMutableUpdate(candidate, value) ==
    /\ MutableInvariant
    /\ candidate \in Candidates
    /\ value \in 1..MaxScore
    /\ mutable_scores' = [mutable_scores EXCEPT ![candidate] = value]
    /\ mutable_extra' = [d \in Candidates |-> 0]
    /\ UNCHANGED <<mutable_weight_total, mutable_max_score>>
    /\ MutableInvariant'

ImplRankedSelect ==
    /\ RankedInvariant
    /\ ranked_selected' \subseteq Candidates
    /\ R!Cardinality(ranked_selected') = K
    /\ ranked_scores' = ranked_scores
    /\ UNCHANGED <<ranked_k, ranked_max_score>>
    /\ RankedInvariant'

ImplRankedUpdate ==
    /\ RankedInvariant
    /\ \E new_scores \in [Candidates -> 0..MaxScore] :
          ranked_scores' = new_scores
    /\ ranked_selected' = {}
    /\ UNCHANGED <<ranked_k, ranked_max_score>>
    /\ RankedInvariant'

HardStep ==
    /\ ((\E s \in Seats : ImplHardEvaluate(s))
        \/ (\E s \in Seats, c \in Candidates, v \in 0..MaxScore :
              ImplHardUpdateScore(s, c, v)))
    /\ UNCHANGED <<soft_weight_total, soft_max_score, soft_scores, soft_extra,
                    mutable_weight_total, mutable_max_score, mutable_scores, mutable_extra,
                    ranked_k, ranked_max_score, ranked_selected, ranked_scores>>
SoftStep ==
    /\ ImplSoftAssign
    /\ UNCHANGED <<hard_num_seats, hard_num_candidates, hard_max_score,
                    hard_allocation, hard_scores,
                    mutable_weight_total, mutable_max_score, mutable_scores, mutable_extra,
                    ranked_k, ranked_max_score, ranked_selected, ranked_scores>>
MutableStep ==
    /\ (ImplMutableAssign
        \/ (\E c \in Candidates, v \in 1..MaxScore : ImplMutableUpdate(c, v)))
    /\ UNCHANGED <<hard_num_seats, hard_num_candidates, hard_max_score,
                    hard_allocation, hard_scores,
                    soft_weight_total, soft_max_score, soft_scores, soft_extra,
                    ranked_k, ranked_max_score, ranked_selected, ranked_scores>>
RankedStep ==
    /\ (ImplRankedSelect \/ ImplRankedUpdate)
    /\ UNCHANGED <<hard_num_seats, hard_num_candidates, hard_max_score,
                    hard_allocation, hard_scores,
                    soft_weight_total, soft_max_score, soft_scores, soft_extra,
                    mutable_weight_total, mutable_max_score, mutable_scores, mutable_extra>>
ImplRead == UNCHANGED vars

ImplNext == HardStep \/ SoftStep \/ MutableStep \/ RankedStep \/ ImplRead
Spec == Init /\ [][ImplNext]_vars

HardRefinement == H!Spec
SoftRefinement == S!Spec
MutableSoftRefinement == MS!MutableScoreSpec
RankedRefinement == R!Spec
====
