---- MODULE SelectThenActuate_NEG_WinnerOptimality ----
\* NEGATIVE CONTROL. The base composition is instantiated without copying it.
\* Only Evaluate is replaced: the mutant allocates the lowest-scoring candidate,
\* so the isolated WinnerOptimality check must fail.

EXTENDS Naturals, FiniteSets

CONSTANTS Seats, Candidates, MaxScore, NULL
VARIABLES allocation, scores, effects, complete

vars == <<allocation, scores, effects, complete>>

Base == INSTANCE SelectThenActuate WITH
            Seats      <- Seats,
            Candidates <- Candidates,
            MaxScore   <- MaxScore,
            NULL       <- NULL,
            allocation <- allocation,
            scores     <- scores,
            effects    <- effects,
            complete   <- complete

AP == INSTANCE ActuationPass WITH
          Seats      <- Seats,
          Resources  <- Candidates,
          NULL       <- NULL,
          allocation <- allocation,
          effects    <- effects,
          complete   <- complete

Init == Base!Init
WinnerOptimality == Base!WinnerOptimality

BadEvaluate(s) ==
    /\ allocation[s] = NULL
    /\ LET worst == CHOOSE c \in Candidates :
                        /\ \A other \in Candidates : scores[s][c] <= scores[s][other]
                        /\ \A other \in Candidates :
                               scores[s][c] = scores[s][other] => Base!Pos(c) <= Base!Pos(other)
       IN /\ worst \in Candidates
          /\ AP!Allocate(s, worst)
    /\ UNCHANGED scores

Next ==
    \/ \E s \in Seats : BadEvaluate(s)
    \/ \E s \in Seats, c \in Candidates, v \in 0..MaxScore : Base!UpdateScore(s, c, v)
    \/ \E s \in Seats : Base!Actuate(s)
    \/ Base!Finish
====
