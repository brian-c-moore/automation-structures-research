---- MODULE CompetitiveSelectionSoft ----
(***************************************************************************)
(* Soft competitive selection with a finite representable weight total.     *)
(* Each candidate receives one reserved unit; the remaining Pool units are  *)
(* assigned sequentially by the Webster/Sainte-Lague priority rule. This is *)
(* a discrete realization of positive, normalized, score-order-preserving   *)
(* allocation. It does not model real-valued exponentiation or claim exact  *)
(* softmax correspondence.                                                  *)
(*                                                                          *)
(* weights is derived from the evolving extra allocation. Init reserves one *)
(* unit per candidate; AssignNext awards Pool additional units using         *)
(* priority(c) = scores[c] / (2*extra[c]+1). At Terminal, weights is the    *)
(* completed discrete apportionment for the current scores.                  *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Candidates, WeightTotal, MaxScore, CandidateOrder

\* Composite values stay in TLA+ and the bounded TLC configurations bind the
\* constant by definition substitution.
ConfiguredCandidateOrder == <<"c1", "c2", "c3">>

\* The reserved floor (one guaranteed unit per candidate) requires at least
\* one representable unit per candidate to give out.
ASSUME WeightTotalBound == WeightTotal >= Cardinality(Candidates)

VARIABLES scores, extra

vars == <<scores, extra>>

WN == Cardinality(Candidates)

\* Refinement packages bind this explicit order to their representation order.
\* Keeping it as a constant prevents a silent assumption that CHOOSE order is
\* vector index order.
ASSUME CandidateOrderType ==
    /\ CandidateOrder \in [1..WN -> Candidates]
    /\ \A c \in Candidates : \E i \in 1..WN : CandidateOrder[i] = c
    /\ \A i, j \in 1..WN : CandidateOrder[i] = CandidateOrder[j] => i = j
WEnum == CandidateOrder

\* Inverse of WEnum: a fixed position for each candidate, used only to
\* break exact priority ties deterministically (lowest position wins).
Pos(c) == CHOOSE i \in 1..WN : WEnum[i] = c

Reserved == WN
Pool == WeightTotal - Reserved

\* weights is derived, not a state variable: the reserved unit plus
\* whatever extra units this candidate has been awarded so far.
weights == [c \in Candidates |-> 1 + extra[c]]

\* Running total of weights, as a top-level recursive fold over the fixed
\* bijective enumeration WEnum.  It is declared at top level rather than held
\* inside a LET so that the proof can induct over it.
WSum[i \in 0..WN] ==
    IF i = 0 THEN 0 ELSE WSum[i - 1] + weights[WEnum[i]]

\* Running total of awarded, non-reserved units over the same enumeration.
ExtraSum[i \in 0..WN] ==
    IF i = 0 THEN 0 ELSE ExtraSum[i - 1] + extra[WEnum[i]]

\* The construction is terminal once the awarded-unit count equals Pool.
\* Normalization then follows through the WSum/ExtraSum relation.
Terminal == ExtraSum[WN] = Pool

TypeInvariant ==
    /\ scores \in [Candidates -> 0..MaxScore]
    /\ extra \in [Candidates -> Nat]

\* Weights are non-negative (guaranteed by Nat)
NonNegativity ==
    \A c \in Candidates : weights[c] >= 0

\* The running total never overshoots WeightTotal, at every reachable state:
\* it starts at Reserved (<= WeightTotal by the ASSUME above) and each step
\* adds exactly one, guarded by AssignNext so it never exceeds the total.
BoundedTotal ==
    WSum[WN] <= WeightTotal

\* At Terminal, the weights sum to WeightTotal. The proof relates WSum to
\* ExtraSum using weights[c] = 1 + extra[c].
Normalization ==
    Terminal => WSum[WN] = WeightTotal

\* Every candidate contributes (no zero weights): holds unconditionally,
\* since weights[c] = 1 + extra[c] >= 1 for all c, at every reachable state.
UniversalContribution ==
    \A c \in Candidates : weights[c] > 0

\* A strictly higher score never receives a lower weight.
ScoreOrderPreservation ==
    \A c, d \in Candidates : scores[c] < scores[d] => weights[c] <= weights[d]

\* The tightest tie behaviour compatible with proportionality (the fixed-
\* point framing: plus-or-minus one representable unit), at every reachable
\* state: tied candidates' weights differ by at most one.
TieBoundedness ==
    \A c, d \in Candidates :
        scores[c] = scores[d] => weights[c] <= weights[d] + 1 /\ weights[d] <= weights[c] + 1

\* Next-unit priority (Sainte-Lague / Webster): scores[c] / (2*extra[c]+1),
\* compared by cross-multiplication to avoid division and reals.  Ties are
\* broken by lowest enumeration position.
Prefer(c, d) ==
    \/ scores[c] * (2 * extra[d] + 1) > scores[d] * (2 * extra[c] + 1)
    \/ /\ scores[c] * (2 * extra[d] + 1) = scores[d] * (2 * extra[c] + 1)
       /\ Pos(c) < Pos(d)

\* The unique candidate preferred to every other candidate under Prefer, a
\* strict total order (Pos is a bijection, so it breaks every exact tie).
Winner == CHOOSE c \in Candidates : \A d \in Candidates \ {c} : Prefer(c, d)

Init ==
    /\ scores \in [Candidates -> 1..MaxScore]
    /\ extra = [c \in Candidates |-> 0]

\* Award one pool unit to the current highest-priority candidate.
AssignNext ==
    /\ WSum[WN] < WeightTotal
    /\ extra' = [extra EXCEPT ![Winner] = @ + 1]
    /\ scores' = scores

Next == AssignNext

Spec == Init /\ [][Next]_vars

\* Spec => [](NonNegativity /\ BoundedTotal /\ Normalization /\
\* UniversalContribution /\ ScoreOrderPreservation /\ TieBoundedness): proved as
\* the conjunction of NonNegativitySafety, BoundedTotalSafety,
\* NormalizationSafety, UniversalContributionSafety, ScoreOrderPreservationSafety,
\* TieBoundednessSafety in CompetitiveSelectionSoft_Proof.tla.
====
