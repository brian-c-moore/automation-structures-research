---- MODULE ComputationGraph ----
\* ====================================================================
\* SUBSTRATE SPEC: COMPUTATION GRAPH
\*
\* A typed graph whose nodes are primitive applications and whose edges
\* are data dependencies between applications. This is the substrate the
\* structural-ordering predicates (OrderingClassifier) and the
\* ordering->modality admission relation (AdmissionTable) operate over.
\*
\* The state machine enumerates graphs by adding edges one at a time up
\* to a bound; TLC's reachable state set is then every directed graph on
\* `Nodes` with at most `MaxEdge` edges. Well-formedness must hold on
\* every such graph (expected PASS).
\*
\* The structural operators (Preds, Succs, InDeg, OutDeg, ReachFrom,
\* HasCycle, Acyclic) are defined here and reused by
\* OrderingClassifier and AdmissionTable via EXTENDS.
\*
\* Self-contained: standard-library EXTENDS only, per the modality-spec
\* convention.
\* ====================================================================
EXTENDS Naturals, FiniteSets

CONSTANTS MaxNode, MaxEdge, PrimIds
\* MaxNode : positive natural   -- node identifiers are 1..MaxNode
\* MaxEdge : natural            -- cap on |edges| (bounds the state space)
\* PrimIds : finite set         -- representative primitive identifiers
\*                                 a node may be tagged with (e.g.
\*                                 {"RR","TE","RD","AP"} for
\*                                 ResourceRegistry/TraversalEngine/
\*                                 Reduction/ActuationPass).

Nodes == 1..MaxNode

\* All directed edges with no self-loop. Cycles between primitive
\* applications are edges between distinct nodes; a primitive's own
\* iteration is not a self-loop at this level.
PossibleEdges == {e \in Nodes \X Nodes : e[1] # e[2]}

VARIABLES edges, pmap

vars == <<edges, pmap>>

TypeInvariant ==
    /\ edges \subseteq PossibleEdges
    /\ pmap  \in [Nodes -> PrimIds]

\* ----- Structural operators reused by the classifier and admission relation -----

Preds(n)  == {p \in Nodes : <<p, n>> \in edges}
Succs(n)  == {s \in Nodes : <<n, s>> \in edges}
InDeg(n)  == Cardinality(Preds(n))
OutDeg(n) == Cardinality(Succs(n))

\* One forward expansion step of a node set under the edge relation.
ReachStep(S) == S \cup {b \in Nodes : \E a \in S : <<a, b>> \in edges}

\* Bounded transitive closure. A path in a graph on Nodes has length at
\* most MaxNode, so MaxNode expansions reach the full forward set.
RECURSIVE Closure(_, _)
Closure(S, k) == IF k = 0 THEN S ELSE Closure(ReachStep(S), k - 1)

\* Strict forward reachability from n (n itself only if it lies on a cycle).
ReachFrom(n) == Closure({m \in Nodes : <<n, m>> \in edges}, MaxNode)

HasCycle == \E n \in Nodes : n \in ReachFrom(n)
Acyclic  == ~HasCycle

\* ----- Graph-builder state machine -----

Init ==
    /\ edges = {}
    /\ pmap  = [n \in Nodes |-> CHOOSE p \in PrimIds : TRUE]

AddEdge ==
    /\ Cardinality(edges) < MaxEdge
    /\ \E e \in PossibleEdges :
        /\ e \notin edges
        /\ edges' = edges \cup {e}
    /\ UNCHANGED pmap

\* Re-tag a node with a primitive identifier. Ordering classification is
\* independent of pmap; this action exists so the substrate exercises
\* the typed-mapping structure AdmissionTable consumes.
Retag ==
    /\ \E n \in Nodes, p \in PrimIds :
        pmap' = [pmap EXCEPT ![n] = p]
    /\ UNCHANGED edges

Done == /\ Cardinality(edges) = MaxEdge /\ UNCHANGED vars

Next == AddEdge \/ Retag \/ Done

Spec == Init /\ [][Next]_vars

\* ----- Well-formedness invariants (expected PASS) -----

\* Edge endpoints are nodes (structural; holds by construction).
WfEdgesInNodes ==
    \A e \in edges : e[1] \in Nodes /\ e[2] \in Nodes

\* No self-loop at the primitive-application level.
WfNoSelfLoop ==
    \A e \in edges : e[1] # e[2]

\* The primitive-identifier mapping is total over the node set.
WfPrimMapTotal ==
    pmap \in [Nodes -> PrimIds]

WellFormed == WfEdgesInNodes /\ WfNoSelfLoop /\ WfPrimMapTotal

THEOREM Spec => [](TypeInvariant /\ WellFormed)
====
