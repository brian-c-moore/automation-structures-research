---- MODULE FiniteTopologyStreamGraph_PrematureClosure ----
\* Isolated positive baseline paired with the premature-closure control.
EXTENDS FiniteTopologyStreamGraph_Diamond

GoodNext ==
    \/ Publish("source", "p1")
    \/ RequestClose("sl")

BadSpec == Init /\ [][GoodNext]_vars
====
