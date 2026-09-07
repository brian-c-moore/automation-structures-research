---- MODULE FiniteTopologyStreamGraph_NEG_WrongInputReceipt ----
\* Selected-input control. When both sink inputs are ready at the initial
\* cursor, the mutant consumes the nonselected right input.
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

WrongInputReceipt ==
    /\ "rk" \in ReadyInputs("sink")
    /\ IsFirstReady("sink", "lk")
    /\ queues' = [queues EXCEPT !["rk"] = Tail(@)]
    /\ received' =
        [received EXCEPT !["rk"] = Append(@, Head(queues["rk"]))]
    /\ cursor' = [cursor EXCEPT !["sink"] = NextCursor("rk")]
    /\ selection_valid' = FALSE
    /\ UNCHANGED <<sent, discarded, published, edge_status, reached>>

BadNext == PrepareBothInputs \/ WrongInputReceipt
BadSpec == Init /\ [][BadNext]_vars
====
