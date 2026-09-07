---- MODULE AllocationSnapshot_Proof ----
(* TLAPS proof of AllocationSnapshot safety. *)
EXTENDS AllocationSnapshot, Naturals, FiniteSets, TLAPS

ASSUME BudgetCapacityType == BudgetCapacity \in Nat

Inv == TypeInvariant /\ BudgetConsistency

LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv  OBVIOUS
  <1>1. TypeInvariant
    BY BudgetCapacityType DEF Init, TypeInvariant
  <1>2. BudgetConsistency
    BY BudgetCapacityType DEF Init, BudgetConsistency
  <1> QED  BY <1>1, <1>2 DEF Inv

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'  OBVIOUS
  <1> USE DEF Inv, TypeInvariant, BudgetConsistency
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF vars
  <1>1. CASE Next
    <2> SUFFICES ASSUME NEW n \in Nodes, NEW c \in 1..BudgetCapacity, AcceptNode(n, c)
                 PROVE Inv'
      BY <1>1 DEF Next
    <2>a. accepted' = accepted \cup {n}                 BY DEF AcceptNode
    <2>b. total_cost' = total_cost + c                  BY DEF AcceptNode
    <2>c. budget_remaining' = budget_remaining - c      BY DEF AcceptNode
    <2>d. c <= budget_remaining                         BY DEF AcceptNode
    <2>e. c \in Nat /\ c >= 1                           BY BudgetCapacityType
    <2>1. accepted' \subseteq Nodes                     BY <2>a
    <2>2. total_cost' \in Nat                           BY <2>b, <2>e
    <2>3. budget_remaining' \in Nat                     BY <2>c, <2>d, <2>e
    <2>4. total_cost' + budget_remaining' <= BudgetCapacity
      BY <2>b, <2>c, <2>d, <2>e, BudgetCapacityType
    <2> QED  BY <2>1, <2>2, <2>3, <2>4
  <1> QED  BY <1>0, <1>1

THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv               BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'  BY NextInv
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

THEOREM TypeSafety == Spec => []TypeInvariant                 BY Safety, PTL DEF Inv
THEOREM BudgetConsistencySafety == Spec => []BudgetConsistency  BY Safety, PTL DEF Inv
====
