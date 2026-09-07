---- MODULE QualityHierarchyFromGraphRegistry_NEG ----
\* Refinement negative control. CSetNodeProperties omits the childless and
\* parentless guards, allowing the level or cost of a node on an existing edge
\* to invalidate the target hierarchy obligations. Registry and graph component
\* invariants remain intact, so the refinement property must detect the fault.

EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, MaxLevel, NULL

VARIABLES g_edges, g_adjacency, lvl_entries, cost_entries

vars == <<g_edges, g_adjacency, lvl_entries, cost_entries>>

Vals == 0..MaxLevel

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

ComponentSafety ==
    /\ RG!AdjacencyConsistency
    /\ RG!NoSelfLoops
    /\ LvlReg!UniqueMapping
    /\ CostReg!UniqueMapping

TypeInvariant ==
    /\ RG!TypeInvariant
    /\ LvlReg!TypeInvariant
    /\ CostReg!TypeInvariant

LevelView == [n \in Nodes |->
    IF \E v \in Vals : <<n, v>> \in lvl_entries
    THEN CHOOSE v \in Vals : <<n, v>> \in lvl_entries
    ELSE 0]

CostView == [n \in Nodes |->
    IF \E v \in Vals : <<n, v>> \in cost_entries
    THEN CHOOSE v \in Vals : <<n, v>> \in cost_entries
    ELSE 0]

ChildrenView == g_adjacency

HasParent(c) == \E n \in Nodes : c \in g_adjacency[n]
ParentView == [c \in Nodes |->
    IF HasParent(c) THEN CHOOSE n \in Nodes : c \in g_adjacency[n] ELSE NULL]

Init ==
    /\ RG!Init
    /\ LvlReg!Init
    /\ CostReg!Init

CAddChild(p, c) ==
    /\ c \notin ChildrenView[p]
    /\ ~HasParent(c)
    /\ LevelView[p] > LevelView[c]
    /\ CostView[p] <= CostView[c]
    /\ RG!AddEdge(p, c, 0)
    /\ UNCHANGED <<lvl_entries, cost_entries>>

\* Fault: update properties without proving the node is isolated.
CSetNodeProperties(n, l, c) ==
    /\ LvlReg!Register(n, l)
    /\ CostReg!Register(n, c)
    /\ UNCHANGED <<g_edges, g_adjacency>>

Next ==
    \/ \E p, c \in Nodes : CAddChild(p, c)
    \/ \E n \in Nodes, l \in Vals, c \in Vals : CSetNodeProperties(n, l, c)

Spec == Init /\ [][Next]_vars

QH == INSTANCE QualityHierarchy WITH
        level    <- LevelView,
        cost     <- CostView,
        children <- ChildrenView,
        parent   <- ParentView,
        Nodes    <- Nodes,
        MaxLevel <- MaxLevel,
        NULL     <- NULL

QualityHierarchyRefinement == QH!Spec
====
