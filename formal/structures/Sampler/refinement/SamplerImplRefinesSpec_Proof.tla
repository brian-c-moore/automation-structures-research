---- MODULE SamplerImplRefinesSpec_Proof ----
EXTENDS SamplerImplRefinesSpec, TLAPS

LEMMA InitRefines == Init => S!Init BY DEF Init, S!Init
LEMMA NextRefines == [ImplNext]_vars => [S!Next]_(S!vars)
  <1> SUFFICES ASSUME [ImplNext]_vars PROVE [S!Next]_(S!vars) OBVIOUS
  <1>0. CASE UNCHANGED vars BY <1>0 DEF vars, S!vars
  <1>1. CASE \E i \in Items : ImplSample(i)
    BY <1>1 DEF ImplSample, ImplInvariant, S!Next, S!Sample, S!vars
  <1>2. CASE \E i \in Items : ImplZero(i)
    BY <1>2 DEF ImplZero, ImplInvariant, S!Next, S!Zero
  <1>3. CASE ImplReadOrReject BY <1>3 DEF ImplReadOrReject, vars, S!vars
  <1> QED BY <1>0, <1>1, <1>2, <1>3 DEF ImplNext

THEOREM RefinementThm == Spec => S!Spec
  BY InitRefines, NextRefines, PTL DEF Spec, S!Spec
THEOREM RefinementOriginal == Spec => Refinement
  BY RefinementThm DEF Refinement
====
