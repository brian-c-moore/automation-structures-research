---- MODULE QualityHierarchy ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, MaxLevel, NULL

VARIABLES level, cost, children, parent

vars == <<level, cost, children, parent>>

\* State domains used by the inductive safety proof.
TypeInvariant ==
    /\ level \in [Nodes -> 0..MaxLevel]
    /\ cost \in [Nodes -> Nat]
    /\ children \in [Nodes -> SUBSET Nodes]
    /\ parent \in [Nodes -> Nodes \cup {NULL}]

\* AddChild establishes the three edge obligations. SetNodeProperties changes
\* only a node with no parent or children, preserving every existing edge.

\* Levels strictly decrease from parent to child.
StrictLevelDescent ==
    \A n \in Nodes : \A c \in children[n] : level[n] > level[c]

\* Every child edge agrees with the child's parent pointer.
ParentEdgeAgreement ==
    \A n \in Nodes : \A c \in children[n] : parent[c] = n

\* Cost monotonicity: parent cost <= child cost
CostMonotonicity ==
    \A n \in Nodes : \A c \in children[n] : cost[n] <= cost[c]

Init ==
    /\ level = [n \in Nodes |-> 0]
    /\ cost = [n \in Nodes |-> 0]
    /\ children = [n \in Nodes |-> {}]
    /\ parent = [n \in Nodes |-> NULL]

\* Add one parent-child edge and its matching parent pointer.
AddChild(p, c) ==
    /\ p /= c
    /\ c \notin children[p]
    /\ parent[c] = NULL  \* c has no parent yet
    /\ level[p] > level[c]  \* level constraint checked
    /\ cost[p] <= cost[c]  \* cost monotonicity checked
    /\ children' = [children EXCEPT ![p] = @ \cup {c}]
    /\ parent' = [parent EXCEPT ![c] = p]
    /\ UNCHANGED <<level, cost>>

\* Set level and cost only for a node outside every hierarchy edge.
SetNodeProperties(n, l, c) ==
    /\ children[n] = {}
    /\ parent[n] = NULL
    /\ level' = [level EXCEPT ![n] = l]
    /\ cost' = [cost EXCEPT ![n] = c]
    /\ UNCHANGED <<children, parent>>

Next ==
    \/ \E p, c \in Nodes : AddChild(p, c)
    \/ \E n \in Nodes, l \in 0..MaxLevel, c \in 0..MaxLevel : SetNodeProperties(n, l, c)

Spec == Init /\ [][Next]_vars

\* QualityHierarchy_Proof proves preservation of all three edge obligations.
====
