---- MODULE SelectThenActuate_NEG_ActuationScope ----
\* NEGATIVE CONTROL. The base composition is instantiated without copying it.
\* Only actuation is replaced: the mutant records an effect for an unallocated
\* seat, so the isolated ActuationScope check must fail.

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
ActuationScope == Base!ActuationScope

BadActuate(s, r) ==
    /\ ~complete
    /\ allocation[s] = NULL
    /\ effects[s] = NULL
    /\ effects' = [effects EXCEPT ![s] = r]
    /\ UNCHANGED <<allocation, scores, complete>>

Next ==
    \/ \E s \in Seats : Base!Evaluate(s)
    \/ \E s \in Seats, c \in Candidates, v \in 0..MaxScore : Base!UpdateScore(s, c, v)
    \/ \E s \in Seats, r \in Candidates : BadActuate(s, r)
    \/ Base!Finish
====
