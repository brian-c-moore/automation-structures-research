---- MODULE TraversalEngineImplRefinesSpec_NEG ----
(***************************************************************************)
(* Isolated scheduling atomicity fault: remove two queued nodes in one      *)
(* commit. Budget and accepted-subset invariants remain true, but one       *)
(* canonical Skip action removes exactly one node.                          *)
(***************************************************************************)
\* EXPECT: VIOLATION
EXTENDS TraversalEngineImplRefinesSpec

AdjacentInvariant == ImplInvariant
FaultSkipTwo ==
    /\ AdjacentInvariant
    /\ {1, 2} \subseteq queue
    /\ queue' = queue \ {1, 2}
    /\ UNCHANGED <<num_nodes, root, max_budget,
                    budget_remaining, visited, accepted>>
    /\ AdjacentInvariant'

FaultNext == ImplVisitNode(root) \/ FaultSkipTwo \/ ImplTerminateOrRead
FaultRefinement == T!Spec
====
