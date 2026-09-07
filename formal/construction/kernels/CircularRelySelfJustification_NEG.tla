---- MODULE CircularRelySelfJustification_NEG ----
EXTENDS CommonSemanticSchema

States == [a_ok : BOOLEAN, b_ok : BOOLEAN]

InitialState == [a_ok |-> TRUE, b_ok |-> TRUE]
InitialStates == {InitialState}

InvariantStates == {s \in States : s.a_ok /\ s.b_ok}

StepA ==
    {pair \in States \X States :
        /\ pair[1].a_ok
        /\ pair[2] = [pair[1] EXCEPT !.b_ok = FALSE]}

StepB ==
    {pair \in States \X States :
        /\ pair[1].b_ok
        /\ pair[2] = [pair[1] EXCEPT !.a_ok = FALSE]}

RelyA == StepB
RelyB == StepA

PeerClaimsMatch ==
    PeerReliesDischarged(States, StepA, StepB, RelyA, RelyB)

SchemaAdmitted ==
    AdmittedMutualComposition(
        States, InitialStates, InvariantStates,
        StepA, StepB, {}, {}, RelyA, RelyB)

SchemaRejectsCircularClaims == ~SchemaAdmitted

VARIABLE state

vars == <<state>>

Init == state = InitialState

AAction ==
    /\ state.a_ok
    /\ state' = [state EXCEPT !.b_ok = FALSE]

BAction ==
    /\ state.b_ok
    /\ state' = [state EXCEPT !.a_ok = FALSE]

Next == AAction \/ BAction

Spec == Init /\ [][Next]_vars

ComposedInvariant == state \in InvariantStates

====
