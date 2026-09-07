---- MODULE EquivalenceClassImplRefinesSpec_Proof ----
EXTENDS EquivalenceClassImplRefinesSpec, TLAPS

LEMMA InitRefines == Init => E!Init BY DEF Init, E!Init
LEMMA NextRefines == [ImplNext]_vars => [E!Next]_(E!vars)
  <1> SUFFICES ASSUME [ImplNext]_vars PROVE [E!Next]_(E!vars) OBVIOUS
  <1>0. CASE UNCHANGED vars BY <1>0 DEF vars, E!vars
  <1>1. CASE \E a \in ElementSet, b \in ElementSet : ImplUnion(a, b)
    BY <1>1 DEF ImplUnion, ImplInvariant, E!Next, E!Union
  <1>2. CASE ImplReadOrReject BY <1>2 DEF ImplReadOrReject, vars, E!vars
  <1> QED BY <1>0, <1>1, <1>2 DEF ImplNext

THEOREM RefinementThm == Spec => E!Spec
  BY InitRefines, NextRefines, PTL DEF Spec, E!Spec
THEOREM RefinementOriginal == Spec => Refinement
  BY RefinementThm DEF Refinement
====
