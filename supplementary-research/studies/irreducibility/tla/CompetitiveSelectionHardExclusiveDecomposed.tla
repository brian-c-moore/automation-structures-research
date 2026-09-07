--------------- MODULE CompetitiveSelectionHardExclusiveDecomposed -----------
(* Irreducibility-by-construction for the concept-faithful
   CompetitiveSelectionHardExclusive.

   Hard-mode selection carries two invariants: mutual exclusion (one winner
   per seat) and winner optimality (the winner has the highest score). The
   corpus already carries an instrument for the second:
   CompetitiveSelectionHardDecomposed separates scoring from allocation and a
   concurrent score update makes the cached winner stale. That instrument
   remains the evidence for the optimality half.

   This module is the instrument for the half the pinned spec did not carry.
   The enriched Evaluate reads the pool and awards the seat in ONE step. Here
   that is split: CheckAvailable reads Available(s) and STAGES the winner,
   Commit takes the seat with the staged candidate. Between the two steps
   another seat can read the same pool -- the staged candidate is not yet
   allocated, so it still looks free -- and stage the same candidate. Both
   then commit, and one candidate occupies two seats.

   This is the claim/commit TOCTOU that competing for seats makes unavoidable
   once a candidate can hold at most one: the availability read and the seat
   award are one irreducible operation.

   TLC must find a violation of MutualExclusion.                            *)
EXTENDS Naturals, FiniteSets

CONSTANTS Seats, Candidates, MaxScore, NULL

VARIABLES allocation, scores, staged

vars == <<allocation, scores, staged>>

WN == Cardinality(Candidates)
WEnum == CHOOSE seq \in [1..WN -> Candidates] :
             \A c \in Candidates : \E i \in 1..WN : seq[i] = c
Pos(c) == CHOOSE i \in 1..WN : WEnum[i] = c

Available(s) == {c \in Candidates : \A t \in Seats \ {s} : allocation[t] /= c}

TypeInvariant ==
    /\ allocation \in [Seats -> Candidates \cup {NULL}]
    /\ scores \in [Seats -> [Candidates -> 0..MaxScore]]
    /\ staged \in [Seats -> Candidates \cup {NULL}]

\* The base module's O1, verbatim.
MutualExclusion ==
    \A s, t \in Seats :
        (s /= t /\ allocation[s] /= NULL) => allocation[s] /= allocation[t]

Init ==
    /\ allocation = [s \in Seats |-> NULL]
    /\ scores = [s \in Seats |-> [c \in Candidates |-> 0]]
    /\ staged = [s \in Seats |-> NULL]

(* Step 1 of the split Evaluate: read the pool and stage the winner, WITHOUT
   taking the seat.  The canonical Evaluate does both in one step. *)
CheckAvailable(s) ==
    /\ allocation[s] = NULL
    /\ staged[s] = NULL
    /\ Available(s) /= {}
    /\ LET pool == Available(s)
           best == CHOOSE c \in pool :
                     /\ \A other \in pool : scores[s][other] <= scores[s][c]
                     /\ \A other \in pool :
                           scores[s][other] = scores[s][c] => Pos(c) <= Pos(other)
       IN staged' = [staged EXCEPT ![s] = best]
    /\ UNCHANGED <<allocation, scores>>

(* Step 2 of the split Evaluate: take the seat with the staged candidate.
   The pool was read before the other seat's commit, so this can award a
   candidate another seat has since taken. *)
Commit(s) ==
    /\ staged[s] /= NULL
    /\ allocation' = [allocation EXCEPT ![s] = staged[s]]
    /\ staged'     = [staged EXCEPT ![s] = NULL]
    /\ UNCHANGED scores

(* The live score writer, unchanged from the canonical machine except that it
   also clears any staged claim. *)
UpdateScore(s, c, new_score) ==
    /\ scores'     = [scores EXCEPT ![s][c] = new_score]
    /\ allocation' = [t \in Seats |-> NULL]
    /\ staged'     = [t \in Seats |-> NULL]

Next ==
    \/ \E s \in Seats : CheckAvailable(s)
    \/ \E s \in Seats : Commit(s)
    \/ \E s \in Seats, c \in Candidates, v \in 0..MaxScore : UpdateScore(s, c, v)

Spec == Init /\ [][Next]_vars

\* TLC finds a violation of MutualExclusion.
=============================================================================
