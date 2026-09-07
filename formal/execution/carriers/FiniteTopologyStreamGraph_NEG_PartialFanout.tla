---- MODULE FiniteTopologyStreamGraph_NEG_PartialFanout ----
\* Fan-out atomicity control. The mutant publishes to only one of the source's
\* two outgoing connections while recording one source publication.
EXTENDS FiniteTopologyStreamGraph_Diamond

PartialFanoutPublish ==
    /\ PublishEnabled("source")
    /\ queues' =
        [edge \in StreamEdgesDef |->
            IF edge = "sl" THEN Append(queues[edge], "p1") ELSE queues[edge]]
    /\ sent' =
        [edge \in StreamEdgesDef |->
            IF edge = "sl" THEN Append(sent[edge], "p1") ELSE sent[edge]]
    /\ published' = [published EXCEPT !["source"] = Append(@, "p1")]
    /\ UNCHANGED
        <<received, discarded, edge_status, cursor, reached, selection_valid>>

BadNext == PartialFanoutPublish \/ Next
BadSpec == Init /\ [][BadNext]_vars
====
