---- MODULE CompetitiveSelectionSoftMutableScores_Proof ----
(* TLAPS safety proof for CompetitiveSelectionSoftMutableScores.

   This module extends
   CompetitiveSelectionSoft_Proof, so the Webster priority-order machinery
   (Prefer's transitivity, the maximum-exists argument, WinnerProp) and the
   fold machinery (WSumRec, ExtraSumRec, FoldConstFn, FoldStable,
   WSumExtraSum and their primed twins) are REUSED, and so are `Inv`,
   `InitInv` and `NextInv` themselves.

   What is new is the writer's case, and it is short for a reason worth
   recording: `UpdateScore` lands the system in an INIT-SHAPED state --
   `extra` back at the reserved floor, so every weight is 1 -- with a
   different score vector. So the case is InitInv's argument stated over the
   primed state, and it uses the primed fold twins the base proof already
   carries: a LEMMA is a fact about the CURRENT state, so a primed goal needs
   the primed twin.

   One fact changes its preservation reason.
   `ScorePositive` is an auxiliary invariant carrying Init's tighter
   `scores \in [Candidates -> 1..MaxScore]` forward; the base proof keeps
   it "since scores never changes after Init". Under a live writer it
   survives because the WRITER preserves it -- `UpdateScore` draws the new
   score from the same 1..MaxScore.

   The four base-proof assumptions are inherited unchanged.                *)
EXTENDS CompetitiveSelectionSoftMutableScores, CompetitiveSelectionSoft_Proof

(*-------------------------------------------------------------------------*)
(* The writer's case: a score change invalidates the apportionment, so the  *)
(* post-state is Init-shaped with a different score vector.                 *)
(*-------------------------------------------------------------------------*)
LEMMA UpdateInv ==
  ASSUME Inv, NEW c \in Candidates, NEW v \in 1..MaxScore, UpdateScore(c, v)
  PROVE  Inv'
  <1> USE DEF UpdateScore
  <1>sc. scores' = [scores EXCEPT ![c] = v]   OBVIOUS
  <1>ex. extra' = [d \in Candidates |-> 0]     OBVIOUS
  <1>sp0. \A d \in Candidates : scores[d] > 0  BY DEF Inv, ScorePositive
  <1>st. scores \in [Candidates -> 0..MaxScore]  BY DEF Inv, TypeInvariant

  <1>ty. TypeInvariant'
    <2>1. scores' \in [Candidates -> 0..MaxScore]
      BY <1>sc, <1>st, MaxScoreType
    <2>2. extra' \in [Candidates -> Nat]  BY <1>ex
    <2> QED  BY <2>1, <2>2 DEF TypeInvariant
  <1>sp. ScorePositive'
    <2> SUFFICES ASSUME NEW d \in Candidates PROVE scores'[d] > 0
      BY DEF ScorePositive
    \* Function application after an EXCEPT must come from the EXCEPT and the
    \* function space, not from the pointwise shape alone.
    <2>1. CASE d = c
      <3>1. scores'[d] = v  BY <1>sc, <1>st, <2>1
      <3> QED  BY <3>1
    <2>2. CASE d /= c
      <3>1. scores'[d] = scores[d]  BY <1>sc, <1>st, <2>2
      <3> QED  BY <3>1, <1>sp0
    <2> QED  BY <2>1, <2>2

  \* Every weight is back at the reserved floor: this is what makes the four
  \* pointwise obligations immediate, exactly as at Init.
  <1>wc. \A d \in Candidates : weights'[d] = 1  BY <1>ex DEF weights
  <1>wnat. weights' \in [Candidates -> Nat]     BY <1>wc DEF weights
  <1>nn. NonNegativity'   BY <1>wnat DEF NonNegativity
  <1>uc. UniversalContribution'  BY <1>wc DEF UniversalContribution
  <1>sm. ScoreOrderPreservation' BY <1>wc DEF ScoreOrderPreservation
  <1>tb. TieBoundedness'         BY <1>wc DEF TieBoundedness

  <1>bt. BoundedTotal'
    <2>rec. WSum' = [i \in 0..WN |-> IF i = 0 THEN 0 ELSE WSum'[i - 1] + weights'[WEnum[i]]]
      BY WSumRecPrime
    <2>fold. \A i \in 0..WN : WSum'[i] = i
      BY <1>wnat, <1>wc, <2>rec, FoldConstFn
    <2>final. WSum'[WN] = WN  BY <2>fold, WNType
    <2>cardbound. Cardinality(Candidates) <= WeightTotal  BY WeightTotalBound
    <2>bound. WN <= WeightTotal  BY <2>cardbound DEF WN
    <2> QED  BY <2>final, <2>bound DEF BoundedTotal
  <1>extranat. extra' \in [Candidates -> Nat]  BY <1>ex
  <1>norm. Normalization'
    <2> SUFFICES ASSUME Terminal' PROVE WSum'[WN] = WeightTotal
      BY DEF Normalization
    <2>ext. ExtraSum'[WN] = Pool  BY DEF Terminal
    <2>rel. WSum'[WN] = ExtraSum'[WN] + WN  BY <1>extranat, WSumExtraSumPrime
    <2>arith. Pool + WN = WeightTotal
      BY WeightTotalBound, WeightTotalType, WNType DEF Pool, Reserved
    <2> QED  BY <2>ext, <2>rel, <2>arith
  <1> QED  BY <1>ty, <1>sp, <1>nn, <1>bt, <1>norm, <1>uc, <1>sm, <1>tb DEF Inv

(*-------------------------------------------------------------------------*)
(* The combined step lemma: the base NextInv covers the award and the       *)
(* stutter; UpdateInv covers the writer.                                    *)
(*-------------------------------------------------------------------------*)
LEMMA MutableScoreNextInv == Inv /\ [MutableScoreNext]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [MutableScoreNext]_vars PROVE Inv'  OBVIOUS
  <1>0. CASE UNCHANGED vars
    BY <1>0, NextInv
  <1>1. CASE AssignNext
    <2>1. [Next]_vars  BY <1>1 DEF Next
    <2> QED  BY <2>1, NextInv
  <1>2. CASE \E c \in Candidates, v \in 1..MaxScore : UpdateScore(c, v)
    BY <1>2, UpdateInv
  <1> QED  BY <1>0, <1>1, <1>2 DEF MutableScoreNext

(*-------------------------------------------------------------------------*)
(* Safety over the enriched specification.                                  *)
(*-------------------------------------------------------------------------*)
THEOREM MutableScoreSafety == MutableScoreSpec => []Inv
  <1>1. Init => Inv                       BY InitInv
  <1>2. Inv /\ [MutableScoreNext]_vars => Inv'    BY MutableScoreNextInv
  <1> QED  BY <1>1, <1>2, PTL DEF MutableScoreSpec

THEOREM MutableScoreTypeSafety == MutableScoreSpec => []TypeInvariant
  BY MutableScoreSafety, PTL DEF Inv
THEOREM MutableScoreNonNegativitySafety == MutableScoreSpec => []NonNegativity
  BY MutableScoreSafety, PTL DEF Inv
THEOREM MutableScoreBoundedTotalSafety == MutableScoreSpec => []BoundedTotal
  BY MutableScoreSafety, PTL DEF Inv
THEOREM MutableScoreNormalizationSafety == MutableScoreSpec => []Normalization
  BY MutableScoreSafety, PTL DEF Inv
THEOREM MutableScoreUniversalContributionSafety == MutableScoreSpec => []UniversalContribution
  BY MutableScoreSafety, PTL DEF Inv
THEOREM MutableScoreOrderPreservationSafety == MutableScoreSpec => []ScoreOrderPreservation
  BY MutableScoreSafety, PTL DEF Inv
THEOREM MutableScoreTieBoundednessSafety == MutableScoreSpec => []TieBoundedness
  BY MutableScoreSafety, PTL DEF Inv
====
