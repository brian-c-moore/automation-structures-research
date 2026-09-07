---- MODULE SelectThenActuate ----
\* Compose per-seat hard selection with the canonical ActuationPass lifecycle.
\*
\* Selection owns scores and the winning allocation. ActuationPass owns the
\* allocation/effect handoff and closure. The shared allocation is written only
\* through ActuationPass actions:
\*   Evaluate    = choose a winner + ActuationPass.Allocate
\*   UpdateScore = invalidate a pending winner + ActuationPass.Deallocate
\*   Actuate     = ActuationPass.Actuate
\*   Finish      = ActuationPass.Finish
\*
\* UpdateScore is disabled after an effect has been applied. ActuationPass owns
\* an applied seat until closure; clearing an effect record would not undo the
\* external effect.

EXTENDS Naturals, FiniteSets

CONSTANTS Seats, Candidates, MaxScore, NULL

VARIABLES allocation, scores, effects, complete

vars == <<allocation, scores, effects, complete>>
actuationVars == <<allocation, effects, complete>>

AP == INSTANCE ActuationPass WITH
          Seats      <- Seats,
          Resources  <- Candidates,
          NULL       <- NULL,
          allocation <- allocation,
          effects    <- effects,
          complete   <- complete

\* Fixed candidate enumeration for deterministic lowest-position ties.
WN == Cardinality(Candidates)
WEnum == CHOOSE seq \in [1..WN -> Candidates] :
             \A c \in Candidates : \E i \in 1..WN : seq[i] = c
Pos(c) == CHOOSE i \in 1..WN : WEnum[i] = c

TypeInvariant ==
    /\ AP!TypeInvariant
    /\ scores \in [Seats -> [Candidates -> 0..MaxScore]]

Actuated == AP!Actuated
ActuationScope == AP!ActuationScope
EffectFidelity == AP!EffectFidelity
PassCompleteness == AP!PassCompleteness

WinnerOptimality ==
    \A s \in Seats :
        allocation[s] /= NULL =>
            \A c \in Candidates :
                scores[s][c] <= scores[s][allocation[s]]

CompositionInvariant ==
    /\ WinnerOptimality
    /\ EffectFidelity
    /\ ActuationScope
    /\ PassCompleteness

Init ==
    /\ allocation = [s \in Seats |-> NULL]
    /\ scores     = [s \in Seats |-> [c \in Candidates |-> 0]]
    /\ effects    = [s \in Seats |-> NULL]
    /\ complete   = FALSE

\* A seat has one pending winner. A score update must invalidate that winner
\* before another evaluation can allocate the seat again.
Evaluate(s) ==
    /\ allocation[s] = NULL
    /\ LET best == CHOOSE c \in Candidates :
                       /\ \A other \in Candidates :
                              scores[s][other] <= scores[s][c]
                       /\ \A other \in Candidates :
                              scores[s][other] = scores[s][c] => Pos(c) <= Pos(other)
       IN /\ best \in Candidates
          /\ AP!Allocate(s, best)
    /\ UNCHANGED scores

\* Selection may revise an unapplied seat. ActuationPass.Deallocate performs
\* the invalidation when a winner exists; an already-unallocated seat stutters
\* at the ActuationPass projection while its score changes.
UpdateScore(s, c, v) ==
    /\ ~complete
    /\ effects[s] = NULL
    /\ scores' = [scores EXCEPT ![s][c] = v]
    /\ IF allocation[s] /= NULL
          THEN AP!Deallocate(s)
          ELSE UNCHANGED actuationVars

Actuate(s) ==
    /\ AP!Actuate(s)
    /\ UNCHANGED scores

Finish ==
    /\ AP!Finish
    /\ UNCHANGED scores

Next ==
    \/ \E s \in Seats : Evaluate(s)
    \/ \E s \in Seats, c \in Candidates, v \in 0..MaxScore : UpdateScore(s, c, v)
    \/ \E s \in Seats : Actuate(s)
    \/ Finish

Spec == Init /\ [][Next]_vars

\* SelectThenActuate_Proof proves that Spec refines the canonical
\* ActuationPass instance and preserves WinnerOptimality.
====
