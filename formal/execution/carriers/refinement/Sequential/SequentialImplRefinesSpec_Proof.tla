---- MODULE SequentialImplRefinesSpec_Proof ----
EXTENDS SequentialImplRefinesSpec, TLAPS

LEMMA InitRefines == Init => S!Init BY DEF Init, S!Init

LEMMA BeginRefines == ImplBeginStep => S!Next
  BY DEF ImplBeginStep, S!Next, S!BeginStep

LEMMA CompleteRefines ==
    \A v \in ValueDomain : ImplCompleteStep(v) => S!Next
  BY DEF ImplCompleteStep, S!Next, S!CompleteStep

LEMMA DoneRefines == ImplDoneStuttering => S!Next
  BY DEF ImplDoneStuttering, S!Next, S!DoneStuttering, vars, S!vars

LEMMA NextRefines == [ImplNext]_vars => [S!Next]_(S!vars)
  <1> SUFFICES ASSUME [ImplNext]_vars PROVE [S!Next]_(S!vars) OBVIOUS
  <1>0. CASE UNCHANGED vars BY <1>0 DEF vars, S!vars
  <1>1. CASE ImplBeginStep BY <1>1, BeginRefines
  <1>2. CASE \E v \in ValueDomain : ImplCompleteStep(v)
    BY <1>2, CompleteRefines
  <1>3. CASE ImplDoneStuttering BY <1>3, DoneRefines
  <1> QED BY <1>0, <1>1, <1>2, <1>3 DEF ImplNext

THEOREM RefinementThm == Spec => S!Spec
  BY InitRefines, NextRefines, PTL DEF Spec, S!Spec, S!vars
====

