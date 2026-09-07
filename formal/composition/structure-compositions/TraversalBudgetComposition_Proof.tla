---- MODULE TraversalBudgetComposition_Proof ----
(* TLAPS proof of TraversalBudgetComposition safety. *)
EXTENDS TraversalBudgetComposition, Naturals, FiniteSets, TLAPS

ASSUME MaxBudgetType == MaxBudget \in Nat
ASSUME RootInNodes == RootNode \in Nodes

Inv == TypeInvariant /\ CompositionInvariant /\ AcceptedSubsetVisited

LEMMA NodeChildrenSubset ==
    \A n : NodeChildren(n) \subseteq Nodes
  <1> SUFFICES ASSUME NEW n PROVE NodeChildren(n) \subseteq Nodes
    OBVIOUS
  <1>1. CASE n = RootNode    BY <1>1 DEF NodeChildren
  <1>2. CASE n /= RootNode   BY <1>2 DEF NodeChildren
  <1> QED  BY <1>1, <1>2

LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv  OBVIOUS
  <1>1. TypeInvariant
    BY MaxBudgetType, RootInNodes DEF Init, TypeInvariant
  <1>2. CompositionInvariant
    BY MaxBudgetType DEF Init, CompositionInvariant
  <1>3. AcceptedSubsetVisited
    BY DEF Init, AcceptedSubsetVisited
  <1> QED  BY <1>1, <1>2, <1>3 DEF Inv

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'  OBVIOUS
  <1> USE DEF Inv, TypeInvariant, CompositionInvariant, AcceptedSubsetVisited
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF vars
  <1>A. CASE \E n \in Nodes : VisitAndAccept(n)
    <2> SUFFICES ASSUME NEW n \in Nodes, VisitAndAccept(n) PROVE Inv'
      BY <1>A
    <2>a. n \in queue                       BY DEF VisitAndAccept
    <2>b. n \notin visited                  BY DEF VisitAndAccept
    <2>c. NodeCost(n) <= budget_remaining   BY DEF VisitAndAccept
    <2>d. NodeCost(n) = 2                   BY DEF NodeCost
    <2>e. accepted' = accepted \cup {n}     BY DEF VisitAndAccept
    <2>f. total_cost' = total_cost + NodeCost(n)  BY DEF VisitAndAccept
    <2>g. budget_remaining' = budget_remaining - NodeCost(n)  BY DEF VisitAndAccept
    <2>h. visited' = visited \cup {n}       BY DEF VisitAndAccept
    <2>i. queue' = (queue \ {n}) \cup NodeChildren(n)  BY DEF VisitAndAccept
    <2>1. accepted' \subseteq Nodes
      BY <2>e
    <2>2. total_cost' \in 0..MaxBudget
      BY <2>c, <2>d, <2>f, MaxBudgetType
    <2>3. budget_remaining' \in 0..MaxBudget
      BY <2>c, <2>d, <2>g, MaxBudgetType
    <2>4. visited' \subseteq Nodes
      BY <2>h
    <2>5. queue' \subseteq Nodes
      BY <2>i, NodeChildrenSubset
    <2>6. total_cost' <= MaxBudget
      BY <2>c, <2>d, <2>f, MaxBudgetType
    <2>7. total_cost' + budget_remaining' = MaxBudget
      BY <2>c, <2>d, <2>f, <2>g, MaxBudgetType
    <2>8. accepted' \subseteq visited'
      BY <2>e, <2>h
    <2> QED  BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8
  <1>B. CASE \E n \in Nodes : SkipUnaffordable(n)
    <2> SUFFICES ASSUME NEW n \in Nodes, SkipUnaffordable(n) PROVE Inv'
      BY <1>B
    <2> QED  BY DEF SkipUnaffordable
  <1>C. CASE \E n \in Nodes : Skip(n)
    <2> SUFFICES ASSUME NEW n \in Nodes, Skip(n) PROVE Inv'
      BY <1>C
    <2> QED  BY DEF Skip
  <1>D. CASE Terminate
    BY <1>D DEF Terminate, vars
  <1>X. CASE Next
    BY <1>X, <1>A, <1>B, <1>C, <1>D DEF Next
  <1> QED  BY <1>0, <1>X

THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv               BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'  BY NextInv
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

THEOREM TypeSafety == Spec => []TypeInvariant       BY Safety, PTL DEF Inv
THEOREM CompositionSafety == Spec => []CompositionInvariant  BY Safety, PTL DEF Inv
THEOREM AcceptedSubsetVisitedSafety == Spec => []AcceptedSubsetVisited  BY Safety, PTL DEF Inv
====
