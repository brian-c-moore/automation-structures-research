---- MODULE FiniteTopologyStreamGraph_StateStreamConfusion ----
\* Isolated positive baseline paired with the state/stream confusion control.
EXTENDS FiniteTopologyStreamGraph_Diamond

VARIABLES expected_stream, last_was_state

control_vars == <<vars, expected_stream, last_was_state>>

ControlInit ==
    /\ Init
    /\ expected_stream = StreamProjection
    /\ last_was_state = FALSE

FramedStateAdvance ==
    /\ AdvanceState("state-left")
    /\ expected_stream' = StreamProjection
    /\ last_was_state' = TRUE

BadNext == FramedStateAdvance
BadSpec == ControlInit /\ [][BadNext]_control_vars

StateStreamFrame == ~last_was_state \/ StreamProjection = expected_stream
====
