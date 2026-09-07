---- MODULE CompetitiveSelectionHardExclusive_NEG_WinnerOptimality ----
\* Negative control for WinnerOptimality. Evaluate selects the lowest-score
\* candidate in the available pool while retaining deterministic tie-breaking.
\* The availability and exclusivity structure match the carrier.

EXTENDS Naturals, FiniteSets

CONSTANTS Seats, Candidates, MaxScore, NULL, CandidateOrder

ConfiguredCandidateOrder == <<"c1", "c2", "c3">>

VARIABLES allocation, scores

vars == <<allocation, scores>>

WN == Cardinality(Candidates)
ASSUME CandidateOrderType ==
    /\ CandidateOrder \in [1..WN -> Candidates]
    /\ \A c \in Candidates : \E i \in 1..WN : CandidateOrder[i] = c
    /\ \A i, j \in 1..WN : CandidateOrder[i] = CandidateOrder[j] => i = j
WEnum == CandidateOrder
Pos(c) == CHOOSE i \in 1..WN : WEnum[i] = c

Available(s) == {c \in Candidates : \A t \in Seats \ {s} : allocation[t] /= c}

TypeInvariant ==
    /\ allocation \in [Seats -> Candidates \cup {NULL}]
    /\ scores \in [Seats -> [Candidates -> 0..MaxScore]]

MutualExclusion ==
    \A s, t \in Seats :
        (s /= t /\ allocation[s] /= NULL) => allocation[s] /= allocation[t]

WinnerOptimality ==
    \A s \in Seats :
        allocation[s] /= NULL =>
            \A c \in Available(s) :
                scores[s][c] <= scores[s][allocation[s]]

WinnerTieBreak ==
    \A s \in Seats :
        allocation[s] /= NULL =>
            \A c \in Available(s) :
                scores[s][c] = scores[s][allocation[s]] => Pos(allocation[s]) <= Pos(c)

Init ==
    /\ allocation = [s \in Seats |-> NULL]
    /\ scores = [s \in Seats |-> [c \in Candidates |-> 0]]

Evaluate(s) ==
    /\ allocation[s] = NULL
    /\ Available(s) /= {}
    /\ LET pool == Available(s)
           best == CHOOSE c \in pool :
\* ---- MUTATION BEGINS -- to the closing marker, this replaces the base text.
                     /\ \A other \in pool : scores[s][c] <= scores[s][other]  \* MUTATED: argmin, not argmax
\* ---- MUTATION ENDS.
                     /\ \A other \in pool :
                           scores[s][other] = scores[s][c] => Pos(c) <= Pos(other)
       IN /\ allocation' = [allocation EXCEPT ![s] = best]
          /\ UNCHANGED scores

UpdateScore(s, c, new_score) ==
    /\ scores' = [scores EXCEPT ![s][c] = new_score]
    /\ allocation' = [t \in Seats |-> NULL]

Next ==
    \/ \E s \in Seats : Evaluate(s)
    \/ \E s \in Seats, c \in Candidates, v \in 0..MaxScore : UpdateScore(s, c, v)

Spec == Init /\ [][Next]_vars

====
