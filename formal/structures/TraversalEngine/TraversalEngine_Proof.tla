---- MODULE TraversalEngine_Proof ----
(***************************************************************************
  TLAPS proof of safety for the TraversalEngine primitive.

  Proves Spec => []Inv, where Inv conjoins the invariants
  TraversalEngine.cfg checks, and a corollary for each of them:
  TypeSafety, AcceptedCostAccountingSafety and
  AcceptedSubsetVisitedSafety. BudgetSafety remains a derived compatibility
  fact because natural-number typing already entails it.
 ***************************************************************************)
EXTENDS TraversalEngine, Naturals, FiniteSets, FiniteSetTheorems, TLAPS

ASSUME MaxBudgetType == MaxBudget \in Nat
ASSUME NodesFinite == IsFiniteSet(Nodes)
\* The .cfg places RootNode in Nodes; the spec does not declare this constraint,
\* but every TLC config satisfies it. Stating it as an ASSUME makes the proof's
\* domain explicit.
ASSUME RootInNodes == RootNode \in Nodes

Inv == TypeInvariant /\ AcceptedCostAccounting /\ AcceptedSubsetVisited

LEMMA NodeChildrenSubset ==
    \A n : NodeChildren(n) \subseteq Nodes
  <1> SUFFICES ASSUME NEW n PROVE NodeChildren(n) \subseteq Nodes
    OBVIOUS
  <1>1. CASE n = RootNode
    BY <1>1 DEF NodeChildren
  <1>2. CASE n /= RootNode
    BY <1>2 DEF NodeChildren
  <1> QED  BY <1>1, <1>2

LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv  OBVIOUS
  <1>1. TypeInvariant
    BY MaxBudgetType, RootInNodes DEF Init, TypeInvariant
  <1>2. AcceptedCostAccounting
    <2>1. Cardinality({}) = 0  BY FS_EmptySet
    <2>2. accepted = {}        BY DEF Init
    <2> QED
      BY <2>1, <2>2, MaxBudgetType
         DEF Init, AcceptedCostAccounting, NodeCost
  <1>3. AcceptedSubsetVisited
    BY DEF Init, AcceptedSubsetVisited
  <1> QED  BY <1>1, <1>2, <1>3 DEF Inv

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'  OBVIOUS
  <1> USE DEF Inv, TypeInvariant, AcceptedCostAccounting,
              AcceptedSubsetVisited
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF vars
  <1>1. CASE Next
    <2>A. CASE \E n \in Nodes : VisitNode(n)
      <3> SUFFICES ASSUME NEW n \in Nodes, VisitNode(n) PROVE Inv'
        BY <2>A
      <3>a. n \in queue                       BY DEF VisitNode
      <3>b. visited' = visited \cup {n}       BY DEF VisitNode
      <3>c. queue \subseteq Nodes             OBVIOUS
      <3>d. visited \subseteq Nodes           OBVIOUS
      <3>e. accepted \subseteq Nodes          OBVIOUS
      <3>f. budget_remaining \in Nat          OBVIOUS
      <3>g. NodeChildren(n) \subseteq Nodes   BY NodeChildrenSubset
      <3>h. NodeCost(n) = 2                   BY DEF NodeCost
      <3>i. accepted \subseteq visited        OBVIOUS
      <3>j. n \notin visited                  BY DEF VisitNode
      <3>k. NodeCost(RootNode) = 2            BY DEF NodeCost
      <3>l. budget_remaining
              + NodeCost(RootNode) * Cardinality(accepted) = MaxBudget
        OBVIOUS
      <3>1. CASE NodeCost(n) <= budget_remaining
        <4>a. accepted' = accepted \cup {n}     BY <3>1 DEF VisitNode
        <4>b. budget_remaining' = budget_remaining - NodeCost(n)
          BY <3>1 DEF VisitNode
        <4>c. queue' = (queue \ {n}) \cup NodeChildren(n)
          BY <3>1 DEF VisitNode
        <4>1. budget_remaining' \in Nat
          BY <3>1, <3>f, <3>h, <4>b
        <4>2. budget_remaining' >= 0
          BY <3>1, <3>f, <3>h, <4>b
        <4>3. visited' \subseteq Nodes
          BY <3>b, <3>d
        <4>4. accepted' \subseteq Nodes
          BY <3>e, <4>a
        <4>5. queue' \subseteq Nodes
          BY <3>c, <3>g, <4>c
        <4>6. accepted' \subseteq visited'
          BY <3>b, <4>a
        <4>7. IsFiniteSet(accepted)
          BY <3>e, NodesFinite, FS_Subset
        <4>7a. Cardinality(accepted) \in Nat
          BY <4>7, FS_CardinalityType
        <4>8. n \notin accepted
          BY <3>i, <3>j
        <4>9. Cardinality(accepted') = Cardinality(accepted) + 1
          BY <4>a, <4>7, <4>8, FS_AddElement
        <4>9f. IsFiniteSet(accepted')
          BY <4>a, <4>7, FS_AddElement
        <4>9n. Cardinality(accepted') \in Nat
          BY <4>9f, FS_CardinalityType
        <4>9a. budget_remaining' + NodeCost(n) = budget_remaining
          BY <3>1, <3>f, <3>h, <4>b
        <4>9b. NodeCost(RootNode) * Cardinality(accepted') =
                  NodeCost(RootNode) * Cardinality(accepted) + NodeCost(n)
          BY <3>h, <3>k, <4>7a, <4>9
        <4>9c. budget_remaining'
                  + NodeCost(RootNode) * Cardinality(accepted') =
                budget_remaining
                  + NodeCost(RootNode) * Cardinality(accepted)
          BY <3>f, <3>h, <3>k, <4>1, <4>7a, <4>9n, <4>9a, <4>9b
        <4>10. AcceptedCostAccounting'
          BY <3>l, <4>9c DEF AcceptedCostAccounting
        <4> QED
          BY <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, <4>10
      <3>2. CASE ~(NodeCost(n) <= budget_remaining)
        <4>a. accepted' = accepted                 BY <3>2 DEF VisitNode
        <4>b. budget_remaining' = budget_remaining BY <3>2 DEF VisitNode
        <4>c. queue' = queue \ {n}                 BY <3>2 DEF VisitNode
        <4>1. budget_remaining' \in Nat            BY <3>f, <4>b
        <4>2. budget_remaining' >= 0               BY <3>f, <4>b
        <4>3. visited' \subseteq Nodes             BY <3>b, <3>d
        <4>4. accepted' \subseteq Nodes            BY <3>e, <4>a
        <4>5. queue' \subseteq Nodes               BY <3>c, <4>c
        <4>6. accepted' \subseteq visited'         BY <3>b, <4>a
        <4>7. AcceptedCostAccounting'
          BY <4>a, <4>b
        <4> QED
          BY <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7
      <3> QED  BY <3>1, <3>2
    <2>B. CASE \E n \in Nodes : Skip(n)
      <3> SUFFICES ASSUME NEW n \in Nodes, Skip(n) PROVE Inv'
        BY <2>B
      <3> QED  BY DEF Skip
    <2>C. CASE Terminate
      BY <2>C DEF Terminate, vars
    <2> QED  BY <2>A, <2>B, <2>C, <1>1 DEF Next
  <1> QED  BY <1>0, <1>1

THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv               BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'  BY NextInv
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

THEOREM TypeSafety == Spec => []TypeInvariant
  BY Safety, PTL DEF Inv

THEOREM AcceptedCostAccountingSafety == Spec => []AcceptedCostAccounting
  BY Safety, PTL DEF Inv

LEMMA TypeImpliesBudgetInvariant == TypeInvariant => BudgetInvariant
  BY DEF TypeInvariant, BudgetInvariant

THEOREM BudgetSafety == Spec => []BudgetInvariant
  <1>1. Spec => []TypeInvariant  BY TypeSafety
  <1>2. TypeInvariant => BudgetInvariant  BY TypeImpliesBudgetInvariant
  <1> QED  BY <1>1, <1>2, PTL

THEOREM AcceptedSubsetVisitedSafety == Spec => []AcceptedSubsetVisited
  BY Safety, PTL DEF Inv

====
