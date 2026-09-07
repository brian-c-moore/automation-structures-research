---- MODULE QualityHierarchyImplRefinesSpec ----
(***************************************************************************)
(* Contract transcription for QualityHierarchy. Vec fields map indexwise  *)
(* to functions; the edge Vec maps to the children relation. num_nodes is  *)
(* also the executable NULL sentinel. Accessors and failed guards stutter.  *)
(***************************************************************************)
\* EXPECT: OK
EXTENDS Naturals, FiniteSets

CONSTANTS NumNodes, MaxLevel
ASSUME NodeCountType == NumNodes \in Nat /\ NumNodes >= 2
ASSUME LevelType == MaxLevel \in Nat /\ MaxLevel >= 1
Nodes == 0..(NumNodes - 1)
Null == NumNodes

VARIABLES num_nodes, max_level, level, cost, children, parent
vars == <<num_nodes, max_level, level, cost, children, parent>>

Q == INSTANCE QualityHierarchy WITH
        Nodes <- Nodes,
        MaxLevel <- MaxLevel,
        NULL <- Null,
        level <- level,
        cost <- cost,
        children <- children,
        parent <- parent

ImplInvariant ==
    /\ num_nodes = NumNodes
    /\ max_level = MaxLevel
    /\ Q!TypeInvariant
    /\ Q!StrictLevelDescent
    /\ Q!ParentEdgeAgreement
    /\ Q!CostMonotonicity

Init ==
    /\ num_nodes = NumNodes
    /\ max_level = MaxLevel
    /\ level = [n \in Nodes |-> 0]
    /\ cost = [n \in Nodes |-> 0]
    /\ children = [n \in Nodes |-> {}]
    /\ parent = [n \in Nodes |-> Null]
    /\ ImplInvariant

ImplAddChild(p, c) ==
    /\ ImplInvariant
    /\ p \in Nodes
    /\ c \in Nodes
    /\ p /= c
    /\ c \notin children[p]
    /\ parent[c] = Null
    /\ level[p] > level[c]
    /\ cost[p] <= cost[c]
    /\ children' = [children EXCEPT ![p] = @ \cup {c}]
    /\ parent' = [parent EXCEPT ![c] = p]
    /\ UNCHANGED <<num_nodes, max_level, level, cost>>
    /\ ImplInvariant'

ImplSetNodeProperties(n, new_level, new_cost) ==
    /\ ImplInvariant
    /\ n \in Nodes
    /\ new_level \in 0..max_level
    /\ new_cost \in 0..max_level
    /\ children[n] = {}
    /\ parent[n] = Null
    /\ level' = [level EXCEPT ![n] = new_level]
    /\ cost' = [cost EXCEPT ![n] = new_cost]
    /\ UNCHANGED <<num_nodes, max_level, children, parent>>
    /\ ImplInvariant'

ImplReadOrReject == UNCHANGED vars
ImplNext ==
    \/ \E p \in Nodes, c \in Nodes : ImplAddChild(p, c)
    \/ \E n \in Nodes, l \in 0..MaxLevel, c \in 0..MaxLevel :
          ImplSetNodeProperties(n, l, c)
    \/ ImplReadOrReject
Spec == Init /\ [][ImplNext]_vars

Refinement == Q!Spec
====
