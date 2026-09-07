---- MODULE FiniteTopologyStreamGraph_PartialFanout ----
\* Isolated positive baseline paired with the partial-fan-out control.
EXTENDS FiniteTopologyStreamGraph_Diamond

AtomicFanoutPublish == Publish("source", "p1")
BadSpec == Init /\ [][AtomicFanoutPublish]_vars
====
