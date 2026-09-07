---- MODULE CompetitiveSelectionHardExclusive ----
(* Exclusive hard selection over multiple seats.

   The advertised obligations are `MutualExclusion`, `WinnerOptimality`, and
   `WinnerTieBreak`. Optimality is relative to `Available(s)`: global argmax
   optimality is incompatible with exclusivity when the same candidate is the
   argmax for more than one seat.

   `Evaluate` fuses the availability check with assignment. Separating those
   operations lets two seats stage the same candidate before either commits.
   A score change clears the whole assignment because seats are coupled through
   availability; clearing only the changed seat could leave another seat with
   a winner that is no longer optimal over its newly enlarged pool.

   This model makes no fill-count, liveness, or coverage claim.               *)
EXTENDS Naturals, FiniteSets

CONSTANTS Seats, Candidates, MaxScore, NULL, CandidateOrder

\* Composite values stay in TLA+ and the bounded TLC configurations bind the
\* constant by definition substitution.
ConfiguredCandidateOrder == <<"c1", "c2", "c3">>

VARIABLES allocation, scores

vars == <<allocation, scores>>

\* Explicit candidate enumeration for deterministic lowest-position
\* tie-breaking. Implementations must bind CandidateOrder at the refinement
\* boundary; no identity with a representation order is implicit.
WN == Cardinality(Candidates)
ASSUME CandidateOrderType ==
    /\ CandidateOrder \in [1..WN -> Candidates]
    /\ \A c \in Candidates : \E i \in 1..WN : CandidateOrder[i] = c
    /\ \A i, j \in 1..WN : CandidateOrder[i] = CandidateOrder[j] => i = j
WEnum == CandidateOrder
Pos(c) == CHOOSE i \in 1..WN : WEnum[i] = c

\* Candidates available to seat s are those held by no other seat.
Available(s) == {c \in Candidates : \A t \in Seats \ {s} : allocation[t] /= c}

\* The invariants are mutually inductive. Evaluate chooses from Available(s),
\* which excludes other seats' winners, and establishes optimality plus the
\* deterministic tie-break over that pool. Later assignments only shrink the
\* pools of unchanged seats. UpdateScore changes one score and atomically clears
\* every assignment, making allocation-indexed obligations vacuous until the
\* next evaluations.
TypeInvariant ==
    /\ allocation \in [Seats -> Candidates \cup {NULL}]
    /\ scores \in [Seats -> [Candidates -> 0..MaxScore]]

\* No non-NULL candidate occupies two distinct seats.
MutualExclusion ==
    \A s, t \in Seats :
        (s /= t /\ allocation[s] /= NULL) => allocation[s] /= allocation[t]

\* The winner has maximal score among candidates still available to the seat.
WinnerOptimality ==
    \A s \in Seats :
        allocation[s] /= NULL =>
            \A c \in Available(s) :
                scores[s][c] <= scores[s][allocation[s]]

\* Among candidates tied with the winner on score, the winner
\* has the lowest enumeration position -- the unique lowest-position argmax
\* over the pool, which is what makes the selection deterministic.
WinnerTieBreak ==
    \A s \in Seats :
        allocation[s] /= NULL =>
            \A c \in Available(s) :
                scores[s][c] = scores[s][allocation[s]] => Pos(allocation[s]) <= Pos(c)

Init ==
    /\ allocation = [s \in Seats |-> NULL]
    /\ scores = [s \in Seats |-> [c \in Candidates |-> 0]]

\* The availability read and seat assignment are one atomic action. Separating
\* them permits two seats to stage the same candidate before either commits.
Evaluate(s) ==
    /\ allocation[s] = NULL
    /\ Available(s) /= {}
    /\ LET pool == Available(s)
           best == CHOOSE c \in pool :
                     /\ \A other \in pool : scores[s][other] <= scores[s][c]
                     /\ \A other \in pool :
                           scores[s][other] = scores[s][c] => Pos(c) <= Pos(other)
       IN /\ allocation' = [allocation EXCEPT ![s] = best]
          /\ UNCHANGED scores

\* Because seat pools are coupled through exclusivity, a score change clears
\* the complete assignment and reopens selection.
UpdateScore(s, c, new_score) ==
    /\ scores' = [scores EXCEPT ![s][c] = new_score]
    /\ allocation' = [t \in Seats |-> NULL]

Next ==
    \/ \E s \in Seats : Evaluate(s)
    \/ \E s \in Seats, c \in Candidates, v \in 0..MaxScore : UpdateScore(s, c, v)

Spec == Init /\ [][Next]_vars

\* Spec => [](TypeInvariant /\ MutualExclusion /\ WinnerOptimality /\
\* WinnerTieBreak): proved as TypeSafety, MutualExclusionSafety,
\* WinnerOptimalitySafety and WinnerTieBreakSafety in
\* CompetitiveSelectionHardExclusive_Proof.tla.
====
