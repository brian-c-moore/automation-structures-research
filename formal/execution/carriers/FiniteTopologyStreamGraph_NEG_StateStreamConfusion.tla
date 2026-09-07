---- MODULE FiniteTopologyStreamGraph_NEG_StateStreamConfusion ----
\* Projection-separation control. The mutant combines one state-edge advance
\* with a source stream publication. All ordinary carrier invariants remain
\* satisfiable, but the state-step frame is observably false.
EXTENDS FiniteTopologyStreamGraph_Diamond

VARIABLES expected_stream, last_was_state

control_vars == <<vars, expected_stream, last_was_state>>

ControlInit ==
    /\ Init
    /\ expected_stream = StreamProjection
    /\ last_was_state = FALSE

ConfusedStateAdvance ==
    /\ StateSourceDef("state-left") \in reached
    /\ StateTargetDef("state-left") \notin reached
    /\ PublishEnabled("source")
    /\ reached' = reached \cup {StateTargetDef("state-left")}
    /\ queues' =
        [edge \in StreamEdgesDef |->
            IF edge \in Outgoing("source")
            THEN Append(queues[edge], "p1")
            ELSE queues[edge]]
    /\ sent' =
        [edge \in StreamEdgesDef |->
            IF edge \in Outgoing("source")
            THEN Append(sent[edge], "p1")
            ELSE sent[edge]]
    /\ published' = [published EXCEPT !["source"] = Append(@, "p1")]
    /\ expected_stream' = StreamProjection
    /\ last_was_state' = TRUE
    /\ UNCHANGED
        <<received, discarded, edge_status, cursor, selection_valid>>

BadNext == ConfusedStateAdvance
BadSpec == ControlInit /\ [][BadNext]_control_vars

StateStreamFrame == ~last_was_state \/ StreamProjection = expected_stream
====
