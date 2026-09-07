---- MODULE FiniteTopologyStreamGraph_ReadyWraparound ----
\* Isolated positive baseline paired with the ready-wraparound control.
EXTENDS FiniteTopologyStreamGraph_Diamond

PrepareWrapOrigin ==
    /\ published["left"] = <<>>
    /\ published["right"] = <<>>
    /\ queues["lk"] = <<>>
    /\ queues["rk"] = <<>>
    /\ queues' =
        [queues EXCEPT !["lk"] = <<"p1">>, !["rk"] = <<"p1">>]
    /\ sent' = [sent EXCEPT !["lk"] = <<"p1">>, !["rk"] = <<"p1">>]
    /\ published' =
        [published EXCEPT
            !["left"] = <<"p1">>, !["right"] = <<"p1">>]
    /\ cursor' = [cursor EXCEPT !["sink"] = EdgeOrderDef("rk")]
    /\ UNCHANGED
        <<received, discarded, edge_status, reached, selection_valid>>

CorrectWraparoundReceipt == ReceiveSelected("sink", "rk")

GoodNext == PrepareWrapOrigin \/ CorrectWraparoundReceipt
BadSpec == Init /\ [][GoodNext]_vars
====
