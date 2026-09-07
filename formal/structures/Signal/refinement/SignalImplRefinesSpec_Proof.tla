---- MODULE SignalImplRefinesSpec_Proof ----
EXTENDS SignalImplRefinesSpec, TLAPS

LEMMA InitRefines == Init => S!Init BY DEF Init, S!Init
LEMMA NextRefines == [ImplNext]_vars => [S!Next]_(S!vars)
  <1> SUFFICES ASSUME [ImplNext]_vars PROVE [S!Next]_(S!vars) OBVIOUS
  <1>0. CASE UNCHANGED vars BY <1>0 DEF vars, S!vars
  <1>1. CASE \E v \in Values : ImplSetValue(v)
    BY <1>1 DEF ImplSetValue, ImplInvariant, S!Next, S!SetValue
  <1>2. CASE \E listener \in Listeners : ImplNotifyListener(listener)
    BY <1>2 DEF ImplNotifyListener, ImplInvariant,
                  S!Next, S!NotifyListener
  <1>3. CASE ImplReadOrReject BY <1>3 DEF ImplReadOrReject, vars, S!vars
  <1> QED BY <1>0, <1>1, <1>2, <1>3 DEF ImplNext

THEOREM RefinementThm == Spec => S!Spec
  BY InitRefines, NextRefines, PTL DEF Spec, S!Spec
THEOREM RefinementOriginal == Spec => Refinement
  BY RefinementThm DEF Refinement
====
