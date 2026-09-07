---- MODULE TraversalEngine_Tight ----
\* Focused checking harness for TraversalEngine at MaxBudget = 3. The root
\* costs 2, leaving budget 1; its children therefore take VisitNode's
\* unaffordable branch. The base MaxBudget = 6 configuration exactly fits all
\* three nodes and does not reach that branch.
\*
\* EXTENDS re-exports the carrier's Init, Next, and invariants unchanged; the
\* paired configuration supplies only the tighter constant.

EXTENDS TraversalEngine

====
