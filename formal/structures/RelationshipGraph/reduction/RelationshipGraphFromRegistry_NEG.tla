---- MODULE RelationshipGraphFromRegistry_NEG ----
\* Negative control for the accumulating registry update.
\* AddEdge overwrites a pair's weight set with {w} instead of registering
\* Weights(s,d) \cup {w}. A second insertion at the same pair therefore drops
\* the previous weighted edge. That step is neither a target AddEdge, a target
\* RemoveEdge, nor a stutter, so RelationshipGraphRefinement must be violated.

EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, MaxWeight

KeyPairs == Nodes \X Nodes
WeightSets == SUBSET (0..MaxWeight)

VARIABLES entries

vars == <<entries>>

Registry == INSTANCE ResourceRegistry WITH Keys <- KeyPairs,
                                           Values <- WeightSets

RegistryUnique == Registry!UniqueMapping

Weights(s, d) ==
    IF \E S \in WeightSets : << <<s, d>>, S >> \in entries
    THEN CHOOSE S \in WeightSets : << <<s, d>>, S >> \in entries
    ELSE {}

EdgesView ==
    {e \in Nodes \X Nodes \X (0..MaxWeight) : e[3] \in Weights(e[1], e[2])}

AdjacencyView == [n \in Nodes |-> {d \in Nodes : Weights(n, d) /= {}}]

TypeInvariant ==
    /\ Registry!TypeInvariant
    /\ \A e \in entries : e[2] /= {}
    /\ \A e \in entries : e[1][1] /= e[1][2]

Init ==
    /\ entries = {}

\* Fault: the current weight set is not read back into the registered value.
AddEdge(s, d, w) ==
    /\ s /= d
    /\ Registry!Register(<<s, d>>, {w})

RemoveEdge(s, d) ==
    /\ Weights(s, d) /= {}
    /\ Registry!Deregister(<<s, d>>)

Next ==
    \/ \E s, d \in Nodes, w \in 0..MaxWeight : AddEdge(s, d, w)
    \/ \E s, d \in Nodes : RemoveEdge(s, d)

Spec == Init /\ [][Next]_vars

RG == INSTANCE RelationshipGraph WITH
        edges     <- EdgesView,
        adjacency <- AdjacencyView,
        Nodes     <- Nodes,
        MaxWeight <- MaxWeight,
        AllowSelfLoops <- FALSE

RelationshipGraphRefinement == RG!Spec
====
