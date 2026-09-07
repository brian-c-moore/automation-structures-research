---- MODULE ReductionImplRefinesSpec_Proof ----
EXTENDS ReductionImplRefinesSpec, TLAPS

LEMMA InitRefines == Init => R!Init BY DEF Init, R!Init
LEMMA NextRefines == [ImplNext]_vars => [R!Next]_(R!vars)
  <1> SUFFICES ASSUME [ImplNext]_vars PROVE [R!Next]_(R!vars) OBVIOUS
  <1>0. CASE UNCHANGED vars BY <1>0 DEF vars, R!vars
  <1>1. CASE ImplProcess
    BY <1>1 DEF ImplProcess, ImplInvariant, Add,
                  R!Next, R!Consume, R!vars
  <1>2. CASE ImplReadOrDone BY <1>2 DEF ImplReadOrDone, vars, R!vars
  <1> QED BY <1>0, <1>1, <1>2 DEF ImplNext

THEOREM RefinementThm == Spec => R!Spec
  BY InitRefines, NextRefines, PTL DEF Spec, R!Spec
THEOREM RefinementOriginal == Spec => Refinement
  BY RefinementThm DEF Refinement
====
