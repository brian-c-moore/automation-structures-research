---- MODULE AllocationSnapshotImplRefinesSpec_Proof ----
EXTENDS AllocationSnapshotImplRefinesSpec, TLAPS

Inv == ImplInvariant
LEMMA InitInv == Init => Inv BY DEF Init, Inv
LEMMA NextInv == Inv /\ [ImplNext]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [ImplNext]_vars PROVE Inv' OBVIOUS
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF Inv, ImplInvariant, TypeInvariant, BudgetConsistency, vars
  <1>1. CASE \E n \in NodeSet, cost \in 1..Capacity : ImplAccept(n, cost)
    BY <1>1 DEF ImplAccept, Inv
  <1>2. CASE ImplReadOrReject
    BY <1>2 DEF ImplReadOrReject, Inv, ImplInvariant, TypeInvariant,
                  BudgetConsistency, vars
  <1> QED BY <1>0, <1>1, <1>2 DEF ImplNext

THEOREM InvariantSafety == Spec => []Inv BY InitInv, NextInv, PTL DEF Spec

LEMMA InitRefines == Init => A!Init BY DEF Init, A!Init
LEMMA NextRefines == [ImplNext]_vars => [A!Next]_(A!vars)
  <1> SUFFICES ASSUME [ImplNext]_vars PROVE [A!Next]_(A!vars) OBVIOUS
  <1>0. CASE UNCHANGED vars BY <1>0 DEF vars, A!vars
  <1>1. CASE \E n \in NodeSet, cost \in 1..Capacity : ImplAccept(n, cost)
    BY <1>1 DEF ImplAccept, A!Next, A!AcceptNode
  <1>2. CASE ImplReadOrReject BY <1>2 DEF ImplReadOrReject, vars, A!vars
  <1> QED BY <1>0, <1>1, <1>2 DEF ImplNext

THEOREM RefinementThm == Spec => A!Spec
  BY InitRefines, NextRefines, PTL DEF Spec, A!Spec
THEOREM RefinementOriginal == Spec => Refinement
  BY RefinementThm DEF Refinement
====
