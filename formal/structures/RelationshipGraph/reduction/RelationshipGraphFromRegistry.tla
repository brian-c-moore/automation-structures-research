---- MODULE RelationshipGraphFromRegistry ----
\* ResourceRegistry-backed implementation of RelationshipGraph.
\* Each (source,destination) key stores the nonempty set of weights currently
\* present for that directed pair. EdgesView flattens those sets into weighted
\* triples; AdjacencyView projects the registered pair domain.
\*
\* AddEdge atomically reads the current weight set and registers its union with
\* the new weight. RemoveEdge deregisters the whole pair, matching the target's
\* removal of every weight for that pair. A scalar overwrite is not equivalent:
\* the negative control drops an existing weight on the second insertion.
\*
\* The construction has no held glue variables. ResourceRegistry.UniqueMapping
\* is required so the CHOOSE-based weight-set read is deterministic. The
\* read-modify-write Register step is assumed atomic.

EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, MaxWeight

KeyPairs == Nodes \X Nodes
WeightSets == SUBSET (0..MaxWeight)

\* ResourceRegistry component state (entries). No glue variables.
VARIABLES entries

vars == <<entries>>

\* ResourceRegistry instance and the unique-key obligation used by Weights.
Registry == INSTANCE ResourceRegistry WITH Keys <- KeyPairs,
                                           Values <- WeightSets

RegistryUnique == Registry!UniqueMapping   \* every key maps to at most one value

\* CF-001 Projection: the weight set held under a pair. Total, with the
\* empty set as the reading for an unregistered pair.
Weights(s, d) ==
    IF \E S \in WeightSets : << <<s, d>>, S >> \in entries
    THEN CHOOSE S \in WeightSets : << <<s, d>>, S >> \in entries
    ELSE {}

\* CF-001 Projection: edges as the flattened triple set.
EdgesView ==
    {e \in Nodes \X Nodes \X (0..MaxWeight) : e[3] \in Weights(e[1], e[2])}

\* CF-001 Projection: adjacency as the key-domain view.
AdjacencyView == [n \in Nodes |-> {d \in Nodes : Weights(n, d) /= {}}]

TypeInvariant ==
    /\ Registry!TypeInvariant
    \* Nothing ever registers an empty weight set, so a present key and a
    \* non-empty reading are the same test -- this is what aligns
    \* Deregister's guard with the target's RemoveEdge guard.
    /\ \A e \in entries : e[2] /= {}
    \* No self-pair is ever registered: the source of NoSelfLoops.
    /\ \A e \in entries : e[1][1] /= e[1][2]

Init ==
    /\ entries = {}

\* AddEdge = a read-modify-write Register: the pair's current weight set is
\* read through the projection and re-registered with w added. The Register
\* effect is the primitive's own operation, invoked by name, not a relabeling.
AddEdge(s, d, w) ==
    /\ s /= d
    /\ Registry!Register(<<s, d>>, Weights(s, d) \cup {w})

\* RemoveEdge = Deregister verbatim. The guard is the projection's
\* non-emptiness, which under TypeInvariant is exactly Deregister's own
\* key-present test and exactly the target's "some weight exists" test.
RemoveEdge(s, d) ==
    /\ Weights(s, d) /= {}
    /\ Registry!Deregister(<<s, d>>)

Next ==
    \/ \E s, d \in Nodes, w \in 0..MaxWeight : AddEdge(s, d, w)
    \/ \E s, d \in Nodes : RemoveEdge(s, d)

Spec == Init /\ [][Next]_vars

\* --- Refinement mapping to RelationshipGraph ---
\* Both mapped values are CF-001 Projections over the component's state.
RG == INSTANCE RelationshipGraph WITH
        edges     <- EdgesView,
        adjacency <- AdjacencyView,
        Nodes     <- Nodes,
        MaxWeight <- MaxWeight,
        AllowSelfLoops <- FALSE

\* Every construction behavior must map to a RelationshipGraph behavior.
RelationshipGraphRefinement == RG!Spec

\* The configuration checks this property on the finite instance; the proof
\* module establishes the same refinement parametrically.
====
