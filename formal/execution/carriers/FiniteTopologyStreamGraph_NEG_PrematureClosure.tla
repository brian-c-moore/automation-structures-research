---- MODULE FiniteTopologyStreamGraph_NEG_PrematureClosure ----
\* Lifecycle control. The mutant marks a nonempty connection closed before
\* its queued item has been received or explicitly discarded.
EXTENDS FiniteTopologyStreamGraph_Diamond

PrematureClose ==
    /\ edge_status["sl"] = OpenStatus
    /\ queues["sl"] # <<>>
    /\ edge_status' = [edge_status EXCEPT !["sl"] = ClosedStatus]
    /\ UNCHANGED
        <<queues, sent, received, discarded, published, cursor, reached,
          selection_valid>>

BadNext == PrematureClose \/ Next
BadSpec == Init /\ [][BadNext]_vars
====
