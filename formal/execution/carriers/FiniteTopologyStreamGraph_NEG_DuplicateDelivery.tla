---- MODULE FiniteTopologyStreamGraph_NEG_DuplicateDelivery ----
\* Delivery-exactness control. One queued item is removed but appended twice
\* to the connection's received history.
EXTENDS FiniteTopologyStreamGraph_Diamond

DuplicateDelivery ==
    /\ queues["sl"] # <<>>
    /\ queues' = [queues EXCEPT !["sl"] = Tail(@)]
    /\ received' =
        [received EXCEPT
            !["sl"] = Append(Append(@, Head(queues["sl"])), Head(queues["sl"]))]
    /\ UNCHANGED
        <<sent, discarded, published, edge_status, cursor, reached,
          selection_valid>>

BadNext == DuplicateDelivery \/ Next
BadSpec == Init /\ [][BadNext]_vars
====
