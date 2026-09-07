---- MODULE FiniteTopologyStreamGraph_NEG_CancellationLoss ----
\* Cancellation-conservation control. The mutant drains a cancelled queue
\* without moving its outstanding item into the explicit discard history.
EXTENDS FiniteTopologyStreamGraph_Diamond

LossyCancel ==
    /\ edge_status["sl"] \in {OpenStatus, ClosingStatus}
    /\ queues["sl"] # <<>>
    /\ queues' = [queues EXCEPT !["sl"] = <<>>]
    /\ edge_status' = [edge_status EXCEPT !["sl"] = CancelledStatus]
    /\ UNCHANGED
        <<sent, received, discarded, published, cursor, reached,
          selection_valid>>

BadNext == LossyCancel \/ Next
BadSpec == Init /\ [][BadNext]_vars
====
