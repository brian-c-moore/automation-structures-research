---- MODULE FiniteTopologyStreamGraph_WrongInputReceipt ----
\* Isolated positive baseline paired with the wrong-input control.
EXTENDS FiniteTopologyStreamGraph_Diamond

PrepareBothInputs ==
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
    /\ UNCHANGED
        <<received, discarded, edge_status, cursor, reached, selection_valid>>

GoodNext == PrepareBothInputs \/ ReceiveSelected("sink", "lk")

BadSpec == Init /\ [][GoodNext]_vars
====
