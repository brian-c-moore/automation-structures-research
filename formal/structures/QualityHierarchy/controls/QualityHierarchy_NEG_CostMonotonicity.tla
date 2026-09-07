---- MODULE QualityHierarchy_NEG_CostMonotonicity ----
\* Negative control for CostMonotonicity. AddChild omits the parent-cost guard
\* while preserving strict level descent and parent-pointer agreement.

EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, MaxLevel, NULL

VARIABLES level, cost, children, parent

vars == <<level, cost, children, parent>>

TypeInvariant ==
    /\ level \in [Nodes -> 0..MaxLevel]
    /\ cost \in [Nodes -> Nat]
    /\ children \in [Nodes -> SUBSET Nodes]
    /\ parent \in [Nodes -> Nodes \cup {NULL}]

StrictLevelDescent ==
    \A n \in Nodes : \A c \in children[n] : level[n] > level[c]

ParentEdgeAgreement ==
    \A n \in Nodes : \A c \in children[n] : parent[c] = n

CostMonotonicity ==
    \A n \in Nodes : \A c \in children[n] : cost[n] <= cost[c]

Init ==
    /\ level = [n \in Nodes |-> 0]
    /\ cost = [n \in Nodes |-> 0]
    /\ children = [n \in Nodes |-> {}]
    /\ parent = [n \in Nodes |-> NULL]

AddChild(p, c) ==
    /\ p /= c
    /\ c \notin children[p]
    /\ parent[c] = NULL
\* ---- MUTATION BEGINS -- to the closing marker, this replaces the base text.
    /\ level[p] > level[c]  \* level constraint checked
\* ---- MUTATION ENDS.
    /\ children' = [children EXCEPT ![p] = @ \cup {c}]
    /\ parent' = [parent EXCEPT ![c] = p]
    /\ UNCHANGED <<level, cost>>

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

====
