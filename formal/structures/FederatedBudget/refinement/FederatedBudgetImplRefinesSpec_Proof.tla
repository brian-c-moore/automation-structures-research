---- MODULE FederatedBudgetImplRefinesSpec_Proof ----
EXTENDS FederatedBudgetImplRefinesSpec, TLAPS

LEMMA InitRefines == Init => F!Init BY DEF Init, F!Init

LEMMA NextRefines == [ImplNext]_vars => [F!Next]_(F!vars)
  <1> SUFFICES ASSUME [ImplNext]_vars PROVE [F!Next]_(F!vars) OBVIOUS
  <1>0. CASE UNCHANGED vars BY <1>0 DEF vars, F!vars
  <1>1. CASE \E n \in Pools, a \in 1..MasterCapacity : ImplAllocateSubPool(n, a)
    BY <1>1 DEF ImplAllocateSubPool, ImplInvariant,
                  F!Next, F!AllocateSubPool, F!vars
  <1>2. CASE \E n \in Pools, a \in 1..MasterCapacity : ImplAllocateFromSubPool(n, a)
    BY <1>2 DEF ImplAllocateFromSubPool, ImplInvariant,
                  F!Next, F!AllocateFromSubPool, F!vars
  <1>3. CASE \E n \in Pools, a \in 1..MasterCapacity : ImplReleaseFromSubPool(n, a)
    BY <1>3 DEF ImplReleaseFromSubPool, ImplInvariant,
                  F!Next, F!ReleaseFromSubPool
  <1>4. CASE ImplReadOrReject BY <1>4 DEF ImplReadOrReject, vars, F!vars
  <1> QED BY <1>0, <1>1, <1>2, <1>3, <1>4 DEF ImplNext

THEOREM RefinementThm == Spec => F!Spec
  BY InitRefines, NextRefines, PTL DEF Spec, F!Spec
THEOREM RefinementOriginal == Spec => Refinement
  BY RefinementThm DEF Refinement
====
