---- MODULE TraversalEngineFromGraphBudget_Proof ----
(***************************************************************************
  TLAPS proof of the TraversalEngine refinement.

  Discharges, unbounded and parametric:

      Refinement == Spec => TE!Spec

  i.e. every behaviour of the RelationshipGraph + Budget + walk-glue
  construction is a TraversalEngine behaviour.

  Parametric: MaxBudget is any natural; Nodes is any set containing
  RootNode; MaxWeight is unconstrained (weights are carried by the graph
  component and never read by the walk). No finiteness is needed.

  The proof preserves RelationshipGraph adjacency and no-self-loop
  obligations, the Budget fragment, and the traversal mapping across every
  construction action. It establishes refinement, not that every target
  obligation is supplied by a retained component.
 ***************************************************************************)
EXTENDS TraversalEngineFromGraphBudget, TLAPS

ASSUME MaxBudgetAss == MaxBudget \in Nat
ASSUME RootAss == RootNode \in Nodes

\* The construction's TypeInvariant fixes the Budget fragment (reserved =
\* pending = 0, allocated in 0..MaxBudget) and types the graph component
\* and the walk glue; the two graph obligations are carried alongside it
\* because they are not consequences of typing.
Inv == TypeInvariant /\ GraphAdjacency /\ GraphNoSelfLoops

(*-------------------------------------------------------------------------*)
(* Lemma: Init establishes the inductive invariant.                        *)
(*-------------------------------------------------------------------------*)
LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv
    OBVIOUS
  <1>1. TypeInvariant
    BY MaxBudgetAss, RootAss DEF Init, TypeInvariant
  <1>2. GraphAdjacency
    <2> SUFFICES ASSUME NEW src \in Nodes
                 PROVE adjacency[src] =
                       {dst \in Nodes : \E w \in 0..MaxWeight :
                            <<src, dst, w>> \in edges}
      BY DEF GraphAdjacency, Graph!AdjacencyConsistency
    <2>1. adjacency[src] = {}   BY DEF Init
    <2>2. {dst \in Nodes : \E w \in 0..MaxWeight :
              <<src, dst, w>> \in edges} = {}
      BY DEF Init
    <2> QED BY <2>1, <2>2
  <1>3. GraphNoSelfLoops
    <2> SUFFICES ASSUME NEW n \in Nodes PROVE n \notin adjacency[n]
      BY DEF GraphNoSelfLoops, Graph!NoSelfLoops
    <2>1. adjacency[n] = {}   BY DEF Init
    <2> QED BY <2>1
  <1> QED BY <1>1, <1>2, <1>3 DEF Inv

(*-------------------------------------------------------------------------*)
(* Lemma: every Next step preserves the inductive invariant.               *)
(*-------------------------------------------------------------------------*)
LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <1> USE DEF Inv, TypeInvariant, GraphAdjacency, GraphNoSelfLoops,
              Graph!AdjacencyConsistency, Graph!NoSelfLoops
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF vars
  <1>L. CASE \E s, d \in Nodes, w \in 0..MaxWeight : LoadEdge(s, d, w)
    <2> SUFFICES ASSUME NEW src \in Nodes, NEW dst \in Nodes,
                        NEW w \in 0..MaxWeight, LoadEdge(src, dst, w)
                 PROVE Inv'
      BY <1>L
    <2>a. src /= dst                                    BY DEF LoadEdge
    <2>b. edges' = edges \cup {<<src, dst, w>>}         BY DEF LoadEdge
    <2>c. adjacency' = [adjacency EXCEPT ![src] = @ \cup {dst}]
      BY DEF LoadEdge
    <2>d. UNCHANGED <<b_capacity, b_allocated, b_reserved, b_pending,
                      queue, visited, accepted>>
      BY DEF LoadEdge
    <2>1. TypeInvariant'
      BY <2>b, <2>c, <2>d
    <2>2. GraphAdjacency'
      <3> SUFFICES ASSUME NEW s2 \in Nodes
                   PROVE adjacency'[s2] =
                         {d2 \in Nodes : \E w2 \in 0..MaxWeight :
                              <<s2, d2, w2>> \in edges'}
        OBVIOUS
      <3>A. CASE s2 = src
        <4>1. adjacency'[s2] = adjacency[src] \cup {dst}   BY <2>c, <3>A
        <4>2. adjacency[src] = {d2 \in Nodes : \E w2 \in 0..MaxWeight :
                                   <<src, d2, w2>> \in edges}
          OBVIOUS
        <4>3. {d2 \in Nodes : \E w2 \in 0..MaxWeight :
                   <<s2, d2, w2>> \in edges'} = adjacency[src] \cup {dst}
          BY <2>b, <3>A, <4>2
        <4> QED BY <4>1, <4>3
      <3>B. CASE s2 /= src
        <4>1. adjacency'[s2] = adjacency[s2]              BY <2>c, <3>B
        <4>2. adjacency[s2] = {d2 \in Nodes : \E w2 \in 0..MaxWeight :
                                  <<s2, d2, w2>> \in edges}
          OBVIOUS
        <4>3. {d2 \in Nodes : \E w2 \in 0..MaxWeight :
                   <<s2, d2, w2>> \in edges'} = adjacency[s2]
          BY <2>b, <3>B, <4>2
        <4> QED BY <4>1, <4>3
      <3> QED BY <3>A, <3>B
    <2>3. GraphNoSelfLoops'
      <3> SUFFICES ASSUME NEW n \in Nodes PROVE n \notin adjacency'[n]
        OBVIOUS
      <3>A. CASE n = src
        <4>1. adjacency'[n] = adjacency[src] \cup {dst}    BY <2>c, <3>A
        <4>2. src \notin adjacency[src]                    OBVIOUS
        <4> QED BY <4>1, <4>2, <2>a, <3>A
      <3>B. CASE n /= src
        <4>1. adjacency'[n] = adjacency[n]                 BY <2>c, <3>B
        <4>2. n \notin adjacency[n]                        OBVIOUS
        <4> QED BY <4>1, <4>2
      <3> QED BY <3>A, <3>B
    <2> QED BY <2>1, <2>2, <2>3
  <1>V. CASE \E n \in Nodes : VisitNode(n)
    <2> SUFFICES ASSUME NEW n \in Nodes, VisitNode(n) PROVE Inv'
      BY <1>V
    <2>a. UNCHANGED <<edges, adjacency, b_capacity, b_reserved, b_pending>>
      BY DEF VisitNode
    <2>b. visited' = visited \cup {n}                      BY DEF VisitNode
    <2>c. adjacency[n] \subseteq Nodes                     OBVIOUS
    <2>1. TypeInvariant'
      <3>A. CASE b_allocated + b_reserved + b_pending + Cost(n) <= b_capacity
        <4>1. /\ accepted' = accepted \cup {n}
              /\ b_allocated' = b_allocated + Cost(n)
              /\ queue' = (queue \ {n}) \cup adjacency[n]
          BY <3>A DEF VisitNode
        <4>2. b_allocated' \in 0..MaxBudget
          BY <4>1, <3>A, <2>a, MaxBudgetAss DEF Cost
        <4> QED BY <4>1, <4>2, <2>a, <2>b, <2>c
      <3>B. CASE ~(b_allocated + b_reserved + b_pending + Cost(n) <= b_capacity)
        <4>1. /\ accepted' = accepted
              /\ b_allocated' = b_allocated
              /\ queue' = queue \ {n}
          BY <3>B DEF VisitNode
        <4> QED BY <4>1, <2>a, <2>b
      <3> QED BY <3>A, <3>B
    <2>2. GraphAdjacency' /\ GraphNoSelfLoops'
      BY <2>a
    <2> QED BY <2>1, <2>2
  <1>S. CASE \E n \in Nodes : Skip(n)
    <2> SUFFICES ASSUME NEW n \in Nodes, Skip(n) PROVE Inv'
      BY <1>S
    <2>a. /\ queue' = queue \ {n}
          /\ UNCHANGED <<edges, adjacency, b_capacity, b_allocated,
                         b_reserved, b_pending, visited, accepted>>
      BY DEF Skip
    <2> QED BY <2>a
  <1>T. CASE Terminate
    BY <1>T DEF Terminate, vars
  <1> QED BY <1>0, <1>L, <1>V, <1>S, <1>T DEF Next

(*-------------------------------------------------------------------------*)
(* Safety: the inductive invariant holds in every reachable state.         *)
(*-------------------------------------------------------------------------*)
THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv                    BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'     BY NextInv
  <1> QED BY <1>1, <1>2, PTL DEF Spec

\* The construction's four .cfg-checked invariants, now unbounded.
THEOREM TypeSafety == Spec => []TypeInvariant
  BY Safety, PTL DEF Inv

THEOREM GraphAdjacencySafety == Spec => []GraphAdjacency
  BY Safety, PTL DEF Inv

THEOREM GraphNoSelfLoopsSafety == Spec => []GraphNoSelfLoops
  BY Safety, PTL DEF Inv

THEOREM BudgetSafetySafety == Spec => []BudgetSafety
  <1>1. Inv => BudgetSafety
    BY MaxBudgetAss
       DEF Inv, TypeInvariant, BudgetSafety, Bgt!SafetyInvariant
  <1> QED BY Safety, <1>1, PTL

(*-------------------------------------------------------------------------*)
(* The refinement: Init maps to TE!Init, every step maps to a TE step or a  *)
(* TE stutter. budget_remaining is the projection b_capacity - b_allocated. *)
(*-------------------------------------------------------------------------*)
LEMMA InitRefines == Init => TE!Init
  <1> SUFFICES ASSUME Init PROVE TE!Init
    OBVIOUS
  <1>a. /\ b_capacity = MaxBudget
        /\ b_allocated = 0
        /\ visited = {}
        /\ accepted = {}
        /\ queue = {RootNode}
    BY DEF Init
  <1> QED BY <1>a, MaxBudgetAss DEF TE!Init

LEMMA NextRefines == Inv /\ [Next]_vars => [TE!Next]_(TE!vars)
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE [TE!Next]_(TE!vars)
    OBVIOUS
  <1>c. /\ b_capacity = MaxBudget
        /\ b_allocated \in 0..MaxBudget
        /\ b_reserved = 0
        /\ b_pending = 0
        /\ queue \subseteq Nodes
        /\ visited \subseteq Nodes
        /\ accepted \subseteq Nodes
    BY DEF Inv, TypeInvariant
  <1>0. CASE UNCHANGED vars
    <2>1. UNCHANGED <<b_capacity, b_allocated, visited, accepted, queue>>
      BY <1>0 DEF vars
    <2> QED BY <2>1 DEF TE!vars
  <1>L. CASE \E s, d \in Nodes, w \in 0..MaxWeight : LoadEdge(s, d, w)
    \* Loading the graph moves no mapped variable: a TE stutter.
    <2>1. UNCHANGED <<b_capacity, b_allocated, visited, accepted, queue>>
      BY <1>L DEF LoadEdge
    <2> QED BY <2>1 DEF TE!vars
  <1>V. CASE \E n \in Nodes : VisitNode(n)
    <2> SUFFICES ASSUME NEW n \in Nodes, VisitNode(n)
                 PROVE [TE!Next]_(TE!vars)
      BY <1>V
    <2>a. /\ FullTopology
          /\ n \in queue
          /\ n \notin visited
          /\ visited' = visited \cup {n}
          /\ UNCHANGED <<edges, adjacency, b_capacity, b_reserved, b_pending>>
      BY DEF VisitNode
    \* The frontier expansion uses the graph's adjacency; the walk gate makes
    \* it equal the target's own NodeChildren.
    <2>b. adjacency[n] = TE!NodeChildren(n)
      BY <2>a DEF FullTopology, TargetChildren, TE!NodeChildren
    <2>1. TE!VisitNode(n)
      <3>A. CASE b_allocated + b_reserved + b_pending + Cost(n) <= b_capacity
        <4>1. /\ accepted' = accepted \cup {n}
              /\ b_allocated' = b_allocated + Cost(n)
              /\ queue' = (queue \ {n}) \cup adjacency[n]
          BY <3>A DEF VisitNode
        \* The construction's affordability guard IS the target's, read
        \* through the projection: reserved and pending are pinned at 0.
        <4>2. TE!NodeCost(n) <= b_capacity - b_allocated
          BY <3>A, <1>c, MaxBudgetAss DEF Cost, TE!NodeCost
        <4>3. b_capacity' - b_allocated' =
              (b_capacity - b_allocated) - TE!NodeCost(n)
          BY <4>1, <2>a, <1>c, MaxBudgetAss DEF Cost, TE!NodeCost
        <4> QED BY <4>1, <4>2, <4>3, <2>a, <2>b DEF TE!VisitNode
      <3>B. CASE ~(b_allocated + b_reserved + b_pending + Cost(n) <= b_capacity)
        <4>1. /\ accepted' = accepted
              /\ b_allocated' = b_allocated
              /\ queue' = queue \ {n}
          BY <3>B DEF VisitNode
        <4>2. ~(TE!NodeCost(n) <= b_capacity - b_allocated)
          BY <3>B, <1>c, MaxBudgetAss DEF Cost, TE!NodeCost
        <4>3. b_capacity' - b_allocated' = b_capacity - b_allocated
          BY <4>1, <2>a
        <4> QED BY <4>1, <4>2, <4>3, <2>a DEF TE!VisitNode
      <3> QED BY <3>A, <3>B
    <2> QED BY <2>1 DEF TE!Next
  <1>S. CASE \E n \in Nodes : Skip(n)
    <2> SUFFICES ASSUME NEW n \in Nodes, Skip(n)
                 PROVE [TE!Next]_(TE!vars)
      BY <1>S
    <2>a. /\ n \in queue
          /\ queue' = queue \ {n}
          /\ UNCHANGED <<b_capacity, b_allocated, visited, accepted>>
      BY DEF Skip
    <2>1. TE!Skip(n)
      BY <2>a DEF TE!Skip
    <2> QED BY <2>1 DEF TE!Next
  <1>T. CASE Terminate
    <2>a. queue = {} /\ UNCHANGED vars
      BY <1>T DEF Terminate
    <2>1. UNCHANGED <<b_capacity, b_allocated, visited, accepted, queue>>
      BY <2>a DEF vars
    <2> QED BY <2>1 DEF TE!vars
  <1> QED BY <1>0, <1>L, <1>V, <1>S, <1>T DEF Next

(*-------------------------------------------------------------------------*)
(* The main result: the construction refines TraversalEngine.              *)
(*-------------------------------------------------------------------------*)
THEOREM Refinement == Spec => TE!Spec
  <1>1. Init => TE!Init                              BY InitRefines
  <1>2. Inv /\ [Next]_vars => [TE!Next]_(TE!vars)    BY NextRefines
  <1>3. Spec => []Inv                                BY Safety
  <1> QED BY <1>1, <1>2, <1>3, PTL DEF Spec, TE!Spec

\* Restatement in the base module's own vocabulary.
THEOREM RefinementOriginal == Spec => TERefinement
  BY Refinement DEF TERefinement

====
