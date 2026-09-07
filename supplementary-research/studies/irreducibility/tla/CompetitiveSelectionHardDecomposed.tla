------------------ MODULE CompetitiveSelectionHardDecomposed ------------------
(* Decomposition of hard competitive selection: separates scoring from
   allocation. Concurrent score updates between BatchScore and BatchAllocate
   cause stale cached scores → wrong winner. TLC finds WinnerOptimality
   violated.

   Divergences from the single-seat hard-selection structure this names.
   BatchScore and
   BatchAllocate are canonical Evaluate's fused check and act, with
   ConcurrentScoreUpdate in the window, but the split is not the only change
   and none of the rest is required by it:

     - the SEAT DIMENSION is gone. The state here is a single `winner`, where
       canonical allocates over Seats and holds scores per seat;
     - `Candidates` is a local literal here, where canonical declares it a
       CONSTANT;
     - the tie-break machinery is absent. Canonical breaks exact score ties by
       lowest enumeration position (WEnum/Pos) and carries a WinnerTieBreak
       invariant; BatchAllocate picks with \E where canonical Evaluate uses
       CHOOSE, so the winner here is nondeterministic among argmaxes and
       unique there;
     - `Reset` corresponds to no canonical action;
     - `Init` seeds scores at 1 where canonical seeds 0;
     - ConcurrentScoreUpdate changes a score WITHOUT invalidating the
       allocation, where canonical UpdateScore sets that seat's allocation to
       NULL in the same step. That invalidation is what keeps canonical
       WinnerOptimality true across a score change;
     - the shared name `WinnerOptimality` denotes a single-winner predicate
       here and canonical's per-seat one there, and this .cfg checks that one
       invariant where the canonical .cfg checks three.

   The violation is still the split's: ConcurrentScoreUpdate is guarded by
   pc = "scored", so it can fire only inside the defused window and cannot
   produce a stale winner on its own.                                        *)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT MaxScore    \* e.g. 3
CONSTANT NULL

VARIABLE scores, cached_scores, winner, pc

vars == <<scores, cached_scores, winner, pc>>

Candidates == {"c1", "c2", "c3"}

Init ==
    /\ scores = [c \in Candidates |-> 1]
    /\ cached_scores = [c \in Candidates |-> 0]
    /\ winner = NULL
    /\ pc = "idle"

(* Step 1: snapshot current scores *)
BatchScore ==
    /\ pc = "idle"
    /\ cached_scores' = scores
    /\ pc' = "scored"
    /\ UNCHANGED <<scores, winner>>

(* Step 2: pick winner from cached scores *)
BatchAllocate ==
    /\ pc = "scored"
    /\ \E w \in Candidates :
        /\ \A c \in Candidates : cached_scores[w] >= cached_scores[c]
        /\ winner' = w
    /\ pc' = "allocated"
    /\ UNCHANGED <<scores, cached_scores>>

(* Concurrent: environment changes a live score between steps *)
ConcurrentScoreUpdate ==
    /\ pc = "scored"   \* happens between score and allocate
    /\ \E c \in Candidates, v \in 0..MaxScore :
        /\ scores' = [scores EXCEPT ![c] = v]
    /\ UNCHANGED <<cached_scores, winner, pc>>

(* Reset to try again *)
Reset ==
    /\ pc = "allocated"
    /\ pc' = "idle"
    /\ winner' = NULL
    /\ UNCHANGED <<scores, cached_scores>>

Next ==
    \/ BatchScore
    \/ BatchAllocate
    \/ ConcurrentScoreUpdate
    \/ Reset

(* Winner should have the highest CURRENT score *)
WinnerOptimality ==
    winner # NULL =>
        \A c \in Candidates : scores[winner] >= scores[c]

Spec == Init /\ [][Next]_vars
=============================================================================
