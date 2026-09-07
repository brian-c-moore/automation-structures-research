---------- MODULE CompetitiveSelectionSoftMutableScoresDecomposed -----------
(* Irreducibility-by-construction for the concept-faithful
   CompetitiveSelectionSoftMutableScores.

   This module is CompetitiveSelectionSoftMutableScores with EXACTLY ONE
   change: the fused priority-and-award step of `AssignNext` is split into
   ComputeWinner (compute the current Webster highest-priority candidate and
   cache it) and AwardCached (give the unit to the cached candidate).
   Nothing else is weakened -- the writer, the constants, the priority order
   and the invariants are the base module's, and it EXTENDS them rather than
   restating them so that is mechanically true rather than checked by diff.

   The split factors the softmax step into computing the score-derived
   quantity and then applying it, in the fixed-point discretization the
   entry's own header declares as its ceiling. It runs against the enriched
   model, which carries a live score writer: the pinned
   CompetitiveSelectionSoft.tla freezes `scores`, so the concurrent score
   update cannot occur there at all.

   This module is soft's atomicity evidence; the corpus's other soft
   instrument is not. irreducibility/CompetitiveSelectionSoftDecomposed is
   not a decomposition of the module it names -- it attributes the canonical
   module a `Redistribute` action the canonical module does not have (its
   only action is `AssignNext`), holds `weights` as a state variable where
   the canonical module derives it, and fixes its own candidate set.

   TLC must find a violation: the winner is computed against one score
   vector, a concurrent update replaces that vector (invalidating the
   apportionment it was computed against), and the deferred award then lands
   on a candidate the NEW scores rank strictly lower, so the weight vector no
   longer tracks the scores. ScoreOrderPreservation breaks; the sum-based
   obligations (BoundedTotal, Normalization, UniversalContribution,
   NonNegativity) all hold in that state, because a unit is still awarded
   exactly once. The obligations are stated separately so that this
   independence is measurable.                                            *)
EXTENDS CompetitiveSelectionSoftMutableScores

VARIABLES cached,   \* the split-out computation: the winner, computed but
                    \* not yet awarded
          phase     \* "idle" = no award in flight; "computed" = one is

dvars == <<scores, extra, cached, phase>>

DTypeInvariant ==
    /\ TypeInvariant
    /\ cached \in Candidates
    /\ phase \in {"idle", "computed"}

DInit ==
    /\ Init
    /\ cached \in Candidates
    /\ phase = "idle"

(* THE SPLIT -- step 1: compute the current highest-priority candidate. *)
ComputeWinner ==
    /\ phase = "idle"
    /\ WSum[WN] < WeightTotal
    /\ cached' = Winner
    /\ phase' = "computed"
    /\ UNCHANGED <<scores, extra>>

(* THE SPLIT -- step 2: award the unit to the candidate computed earlier. *)
AwardCached ==
    /\ phase = "computed"
    /\ extra' = [extra EXCEPT ![cached] = @ + 1]
    /\ phase' = "idle"
    /\ UNCHANGED <<scores, cached>>

(* The environment, unchanged from the base module. *)
DUpdateScore(c, v) ==
    /\ UpdateScore(c, v)
    /\ UNCHANGED <<cached, phase>>

DNext ==
    \/ ComputeWinner
    \/ AwardCached
    \/ \E c \in Candidates, v \in 1..MaxScore : DUpdateScore(c, v)

DSpec == DInit /\ [][DNext]_dvars

\* TLC finds a violation of ScoreOrderPreservation.
=============================================================================
