---- MODULE FiniteTopologyStreamGraph_CancellationLoss ----
\* Isolated positive baseline paired with the cancellation-loss control.
EXTENDS FiniteTopologyStreamGraph_Diamond

GoodNext ==
    \/ Publish("source", "p1")
    \/ Cancel("sl")

BadSpec == Init /\ [][GoodNext]_vars
====
