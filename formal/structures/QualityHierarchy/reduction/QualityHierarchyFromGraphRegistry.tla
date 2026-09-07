---- MODULE QualityHierarchyFromGraphRegistry ----
\* QualityHierarchy represented by one RelationshipGraph and two
\* ResourceRegistry instances for levels and costs. All target variables are
\* derived from component state; the construction holds no additional state.
\*
\* Registry uniqueness makes level and cost reads deterministic, and graph
\* adjacency supplies children. Strict level descent and cost monotonicity are
\* cross-component obligations enforced by the fused action guards, not by an
\* individual component.

EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, MaxLevel, NULL

\* Component state. No glue variables.
VARIABLES g_edges, g_adjacency,   \* RelationshipGraph<child edges>
          lvl_entries,            \* ResourceRegistry<Nodes -> Level>
          cost_entries            \* ResourceRegistry<Nodes -> Cost>

vars == <<g_edges, g_adjacency, lvl_entries, cost_entries>>

\* The value domain shared by both registries (the target's own Next draws
\* levels and costs from 0..MaxLevel).
Vals == 0..MaxLevel

\* Component instances.
RG == INSTANCE RelationshipGraph WITH edges     <- g_edges,
                                      adjacency <- g_adjacency,
                                      Nodes     <- Nodes,
                                      MaxWeight <- 0,
                                      AllowSelfLoops <- FALSE

LvlReg == INSTANCE ResourceRegistry WITH entries <- lvl_entries,
                                         Keys    <- Nodes,
                                         Values  <- Vals

CostReg == INSTANCE ResourceRegistry WITH entries <- cost_entries,
                                          Keys    <- Nodes,
                                          Values  <- Vals

\* Component safety predicates.
ComponentSafety ==
    /\ RG!AdjacencyConsistency
    /\ RG!NoSelfLoops
    /\ LvlReg!UniqueMapping
    /\ CostReg!UniqueMapping

TypeInvariant ==
    /\ RG!TypeInvariant
    /\ LvlReg!TypeInvariant
    /\ CostReg!TypeInvariant

\* Derived target views.

\* An unregistered level or cost key reads as 0.
LevelView == [n \in Nodes |->
    IF \E v \in Vals : <<n, v>> \in lvl_entries
    THEN CHOOSE v \in Vals : <<n, v>> \in lvl_entries
    ELSE 0]

CostView == [n \in Nodes |->
    IF \E v \in Vals : <<n, v>> \in cost_entries
    THEN CHOOSE v \in Vals : <<n, v>> \in cost_entries
    ELSE 0]

\* children is the graph adjacency function.
ChildrenView == g_adjacency

\* parent is the inverse of adjacency. CAddChild's ~HasParent guard makes this
\* inverse single-valued.
HasParent(c) == \E n \in Nodes : c \in g_adjacency[n]
ParentView == [c \in Nodes |->
    IF HasParent(c) THEN CHOOSE n \in Nodes : c \in g_adjacency[n] ELSE NULL]

Init ==
    /\ RG!Init
    /\ LvlReg!Init
    /\ CostReg!Init

\* Fuse the level/cost checks with graph edge insertion.
CAddChild(p, c) ==
    /\ c \notin ChildrenView[p]
    /\ ~HasParent(c)
    /\ LevelView[p] > LevelView[c]
    /\ CostView[p] <= CostView[c]
    /\ RG!AddEdge(p, c, 0)
    /\ UNCHANGED <<lvl_entries, cost_entries>>

\* SetNodeProperties: both registries upserted in one step, under the
\* isolation guard that is what keeps the hierarchy constraint from going
\* stale behind an already-placed node.
CSetNodeProperties(n, l, c) ==
    /\ ChildrenView[n] = {}
    /\ ~HasParent(n)
    /\ LvlReg!Register(n, l)
    /\ CostReg!Register(n, c)
    /\ UNCHANGED <<g_edges, g_adjacency>>

Next ==
    \/ \E p, c \in Nodes : CAddChild(p, c)
    \/ \E n \in Nodes, l \in Vals, c \in Vals : CSetNodeProperties(n, l, c)

Spec == Init /\ [][Next]_vars

\* --- Refinement mapping to QualityHierarchy -------------------------------
QH == INSTANCE QualityHierarchy WITH
        level    <- LevelView,
        cost     <- CostView,
        children <- ChildrenView,
        parent   <- ParentView,
        Nodes    <- Nodes,
        MaxLevel <- MaxLevel,
        NULL     <- NULL

\* Target obligations restated over the derived views. They are construction
\* contracts and are not implied by ComponentSafety alone.
MappedStrictLevelDescent ==
    \A n \in Nodes : \A c \in ChildrenView[n] : LevelView[n] > LevelView[c]
MappedCostMonotonicity ==
    \A n \in Nodes : \A c \in ChildrenView[n] : CostView[n] <= CostView[c]
MappedParentEdgeAgreement ==
    \A n \in Nodes : \A c \in ChildrenView[n] : ParentView[c] = n

QualityHierarchyRefinement == QH!Spec
====
