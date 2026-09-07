---- MODULE FiniteTopologyStreamGraph_NEG_ReadyWraparound ----
\* Cyclic-selection control. Prepare a larger-profile state with both sink
\* inputs ready and the cursor at the right input, then incorrectly consume
\* the lower absolute edge order instead of wrapping from the cursor.
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

WrongWraparoundReceipt ==
    /\ cursor["sink"] = EdgeOrderDef("rk")
    /\ "lk" \in ReadyInputs("sink")
    /\ "rk" \in ReadyInputs("sink")
    /\ IsFirstReady("sink", "rk")
    /\ queues' = [queues EXCEPT !["lk"] = Tail(@)]
    /\ received' =
        [received EXCEPT !["lk"] = Append(@, Head(queues["lk"]))]
    /\ cursor' = [cursor EXCEPT !["sink"] = NextCursor("lk")]
    /\ selection_valid' = FALSE
    /\ UNCHANGED <<sent, discarded, published, edge_status, reached>>

BadNext == PrepareWrapOrigin \/ WrongWraparoundReceipt
BadSpec == Init /\ [][BadNext]_vars
====
