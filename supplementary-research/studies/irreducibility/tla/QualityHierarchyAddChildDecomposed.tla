----------------- MODULE QualityHierarchyAddChildDecomposed -----------------
(* Splits QualityHierarchy's AddChild: CheckAddChild holds its guards (distinct
   pair, child unlinked, level and cost order); PerformAddChild adds the link.
   Canonical's own SetNodeProperties retypes an endpoint in the window (both
   are unlinked until the link lands), so the link is committed against a stale
   order, violating HierarchyInvariant. Adds `pc` and `held`.
   (QualityHierarchyDecomposed is this entry's guard ablation.) *)
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, MaxLevel, NULL

VARIABLES level, cost, children, parent, pc, held

vars == <<level, cost, children, parent, pc, held>>

TypeInvariant ==
    /\ level \in [Nodes -> 0..MaxLevel]
    /\ cost \in [Nodes -> Nat]
    /\ children \in [Nodes -> SUBSET Nodes]
    /\ parent \in [Nodes -> Nodes \cup {NULL}]

HierarchyInvariant ==
    \A n \in Nodes : \A c \in children[n] : level[n] > level[c]

ParentConsistency ==
    \A n \in Nodes : \A c \in children[n] : parent[c] = n

CostMonotonicity ==
    \A n \in Nodes : \A c \in children[n] : cost[n] <= cost[c]

Init ==
    /\ level = [n \in Nodes |-> 0]
    /\ cost = [n \in Nodes |-> 0]
    /\ children = [n \in Nodes |-> {}]
    /\ parent = [n \in Nodes |-> NULL]
    /\ pc = "idle"
    /\ held = [p |-> NULL, c |-> NULL]

(* Step 1: canonical AddChild's five guards, the pair held; no mutation *)
CheckAddChild(p, c) ==
    /\ pc = "idle"
    /\ p /= c
    /\ c \notin children[p]
    /\ parent[c] = NULL
    /\ level[p] > level[c]
    /\ cost[p] <= cost[c]
    /\ held' = [p |-> p, c |-> c]
    /\ pc' = "checked"
    /\ UNCHANGED <<level, cost, children, parent>>

(* Step 2: canonical AddChild's two writes, on guards already passed *)
PerformAddChild ==
    /\ pc = "checked"
    /\ children' = [children EXCEPT ![held.p] = @ \cup {held.c}]
    /\ parent' = [parent EXCEPT ![held.c] = held.p]
    /\ pc' = "idle"
    /\ UNCHANGED <<level, cost, held>>

SetNodeProperties(n, l, c) ==
    /\ children[n] = {}
    /\ parent[n] = NULL
    /\ level' = [level EXCEPT ![n] = l]
    /\ cost' = [cost EXCEPT ![n] = c]
    /\ UNCHANGED <<children, parent, pc, held>>

Next ==
    \/ \E p, c \in Nodes : CheckAddChild(p, c)
    \/ PerformAddChild
    \/ \E n \in Nodes, l \in 0..MaxLevel, c \in 0..MaxLevel : SetNodeProperties(n, l, c)

Spec == Init /\ [][Next]_vars
=============================================================================
