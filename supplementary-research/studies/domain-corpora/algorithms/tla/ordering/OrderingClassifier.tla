---- MODULE OrderingClassifier ----
\* ====================================================================
\* ORDERING CLASSIFIER
\*
\* Four predicates over a ComputationGraph that, by construction,
\* partition every non-empty graph into exactly one structural ordering:
\* Linear, Tree, DAG, Graph-with-cycles.
\*
\* Primary theorem (Partition): for every reachable (well-formed,
\* non-empty) ComputationGraph, exactly one of the four predicates
\* holds. TLC enumerates every directed graph on `Nodes` (the
\* ComputationGraph builder) and checks Partition on each.
\*
\* The graph machinery (edges, Preds/Succs, InDeg/OutDeg,
\* HasCycle, Acyclic, Init/Next/Spec) is inherited from
\* ComputationGraph; only the four predicates and the partition
\* invariant are added here.
\*
\* Treatment of disconnected components (the open choice the corpus
\* classification flags): the predicates are lifted over the graph AS A
\* WHOLE (disjoint-union treatment). A forest of chains is Linear; a
\* forest with branching is Tree; any join (in-degree >= 2) is DAG; any
\* cycle is Graph-with-cycles. This treatment is recorded in REPORT.md.
\* The non-empty precondition is discharged structurally: MaxNode >= 1,
\* so `Nodes` is always non-empty.
\* ====================================================================
EXTENDS ComputationGraph

\* A cycle dominates: it is the sole classifier when present.
IsGraphWithCycles == HasCycle

\* Acyclic, every node has at most one predecessor and one successor:
\* a chain (or a disjoint union of chains / isolated nodes).
IsLinear ==
    /\ Acyclic
    /\ \A n \in Nodes : InDeg(n) <= 1 /\ OutDeg(n) <= 1

\* Acyclic, every node has at most one predecessor, but it is not a
\* chain (some node branches out, OutDeg >= 2).
IsTree ==
    /\ Acyclic
    /\ ~IsLinear
    /\ \A n \in Nodes : InDeg(n) <= 1

\* Acyclic with a join: some node has two or more predecessors.
IsDAG ==
    /\ Acyclic
    /\ \E n \in Nodes : InDeg(n) >= 2

\* ----- Primary theorem: the four predicates partition -----

\* The set of class tags that currently hold. Exactly one must.
HoldingClasses ==
    { c \in {"Linear", "Tree", "DAG", "Cycles"} :
        \/ (c = "Linear" /\ IsLinear)
        \/ (c = "Tree"   /\ IsTree)
        \/ (c = "DAG"    /\ IsDAG)
        \/ (c = "Cycles" /\ IsGraphWithCycles) }

\* Mutually exclusive AND jointly exhaustive over every reachable graph.
Partition == Cardinality(HoldingClasses) = 1

\* Secondary: the empty-edge graph (all nodes isolated) is Linear
\* vacuously -- the generalization of the "single node, no edges -> IsLinear"
\* edge case.
IsolatedIsLinear == (edges = {}) => IsLinear

THEOREM Spec => [](TypeInvariant /\ Partition /\ IsolatedIsLinear)
====
