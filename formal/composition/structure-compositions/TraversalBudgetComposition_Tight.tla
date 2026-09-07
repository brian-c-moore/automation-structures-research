---- MODULE TraversalBudgetComposition_Tight ----
\* Focused checking harness at MaxBudget = 3. Accepting the root costs 2 and
\* leaves budget 1, so SkipUnaffordable is reachable for either child. The base
\* MaxBudget = 6 configuration exactly fits all three nodes.
\*
\* EXTENDS re-exports the carrier definitions unchanged; the paired
\* configuration supplies only the tighter constant.

EXTENDS TraversalBudgetComposition

====
