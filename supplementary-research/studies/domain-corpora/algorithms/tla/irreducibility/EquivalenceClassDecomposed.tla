---- MODULE EquivalenceClassDecomposed ----
(*
  EquivalenceClass decomposed into
    RelationshipGraph  — stores directed edges (a → b) for each union(a,b) call
    ActuationPass      — adds the edge to the graph
    TraversalEngine    — evaluates "same class" by graph reachability

  The governance semantic that is LOST: transitive-closure-via-representative.
  In the primitive, Find returns the same canonical representative for all
  elements in a class, so Transitivity holds by construction (shared root).
  In the decomposed version, the class membership is determined by
  reachability in the edge graph, WITHOUT a canonical representative being
  maintained.  Two ActuationPass steps (union(a,b) and union(b,c)) each add
  a directed edge.  TraversalEngine checks reachability.

  The violation arises because the decomposed model only stores the DIRECT
  union edges, not their transitive closure.  Specifically:
    - union(a,b) adds edge a→b
    - union(b,c) adds edge b→c
  But checking whether a and c are in the same class by reachability requires
  TWO hops (a→b→c).  If the TraversalEngine only follows ONE hop (the
  ActuationPass is per-edge and TraversalEngine is depth-limited in the
  decomposed model), then Transitivity is not guaranteed.

  The "representative" for element e is the direct parent stored in the
  decomposed graph — the first edge out of e, if any.  Two elements are
  "same class" if they share the same direct parent (one hop).  This loses
  the transitive closure.

  Expected VIOLATION of: Transitivity
  (elements a and c may have different one-hop parents even after union(a,b)
   and union(b,c), so Transitivity is violated.)
*)
EXTENDS Naturals, FiniteSets

CONSTANTS
    Elements,   \* finite set of elements (e.g. {"a","b","c","d"})
    MaxOps      \* bound on union operations

VARIABLES
    edges,      \* set of directed edges: set of <<x,y>> pairs (one per union call)
    ops_done    \* number of union calls so far

vars == <<edges, ops_done>>

\* ---- Decomposed representative: first out-edge of e, or e itself ----------
\* (one-hop parent only; transitive closure NOT computed)
DirectParent(e) ==
    LET out == {p[2] : p \in {p \in edges : p[1] = e}}
    IN  IF out = {} THEN e ELSE CHOOSE r \in out : TRUE

\* ---- Invariant under test -------------------------------------------------

\* Transitivity: if a and c share a "class" transitively (a→b, b→c) then
\* DirectParent(a) = DirectParent(c) must hold for the decomposed model to
\* be correct.  But DirectParent only goes ONE hop, so it fails.
Transitivity ==
    \A a \in Elements : \A b \in Elements : \A c \in Elements :
        (/\ <<a, b>> \in edges
         /\ <<b, c>> \in edges)
        => DirectParent(a) = DirectParent(c)

\* ---- Init -----------------------------------------------------------------

Init ==
    /\ edges    = {}
    /\ ops_done = 0

\* ---- RelationshipGraph + ActuationPass: add a directed edge ---------------
\* union(a,b) is decomposed into: RelationshipGraph adds edge a→b;
\* no representative update is performed (that is the governance step lost).

AddEdge(a, b) ==
    /\ ops_done < MaxOps
    /\ a /= b
    /\ <<a, b>> \notin edges   \* avoid duplicate edges
    /\ edges' = edges \cup {<<a, b>>}
    /\ ops_done' = ops_done + 1

Idle ==
    /\ ops_done >= MaxOps
    /\ UNCHANGED vars

Next ==
    \/ \E a \in Elements, b \in Elements : AddEdge(a, b)
    \/ Idle

Spec == Init /\ [][Next]_vars
=============================================================================
