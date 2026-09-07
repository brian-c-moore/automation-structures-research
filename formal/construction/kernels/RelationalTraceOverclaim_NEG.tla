---- MODULE RelationalTraceOverclaim_NEG ----
EXTENDS Naturals

VARIABLES left_observation, right_observation, revealed

vars == <<left_observation, right_observation, revealed>>

Secrets == {0, 1}
LeftSecret == 0
RightSecret == 1

Init ==
    /\ left_observation = 0
    /\ right_observation = 0
    /\ revealed = FALSE

Reveal ==
    /\ ~revealed
    /\ left_observation' = LeftSecret
    /\ right_observation' = RightSecret
    /\ revealed' = TRUE

DoneStuttering ==
    /\ revealed
    /\ UNCHANGED vars

Next == Reveal \/ DoneStuttering

Spec == Init /\ [][Next]_vars

LeftTraceSafety == left_observation \in Secrets
RightTraceSafety == right_observation \in Secrets

LowObservationsEqual == left_observation = right_observation

====
