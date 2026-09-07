---- MODULE SelectThenActuate_NEG_CompositionInvariant ----
\* NEGATIVE CONTROL. The base composition is instantiated without copying it.
\* Only UpdateScore is replaced: the mutant clears an applied allocation while
\* retaining its effect, so the isolated CompositionInvariant check must fail.

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

Init == Base!Init
CompositionInvariant == Base!CompositionInvariant

BadUpdateScore(s, c, v) ==
    /\ ~complete
    /\ scores' = [scores EXCEPT ![s][c] = v]
    /\ allocation' = [allocation EXCEPT ![s] = NULL]
    /\ UNCHANGED <<effects, complete>>

Next ==
    \/ \E s \in Seats : Base!Evaluate(s)
    \/ \E s \in Seats, c \in Candidates, v \in 0..MaxScore : BadUpdateScore(s, c, v)
    \/ \E s \in Seats : Base!Actuate(s)
    \/ Base!Finish
====
