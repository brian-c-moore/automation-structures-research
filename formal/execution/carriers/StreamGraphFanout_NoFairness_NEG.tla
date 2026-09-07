---- MODULE StreamGraphFanout_NoFairness_NEG ----
\* Progress control. The carrier and all safety obligations are unchanged,
\* but the weak-fairness premise is omitted. Infinite stuttering before the
\* first ingest is then a behavior, so EventualDrain must be violated.

EXTENDS StreamGraphFanout

NoFairnessSpec == Init /\ [][Next]_vars
====
