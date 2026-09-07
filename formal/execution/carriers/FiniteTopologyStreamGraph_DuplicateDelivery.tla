---- MODULE FiniteTopologyStreamGraph_DuplicateDelivery ----
\* Isolated positive baseline paired with the duplicate-delivery control.
EXTENDS FiniteTopologyStreamGraph_Diamond

GoodNext ==
    \/ Publish("source", "p1")
    \/ ReceiveSelected("left", "sl")

BadSpec == Init /\ [][GoodNext]_vars
====
