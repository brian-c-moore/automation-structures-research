---- MODULE StepGraphImplRefinesSpec_Proof ----
EXTENDS StepGraphImplRefinesSpec, TLAPS

LEMMA InitRefines == Init => S!Init
  BY DEF Init, Predecessors, S!Init, S!Predecessors

LEMMA ReadyRefines ==
    \A n \in Nodes : ImplBecomeReady(n) => S!Next
  BY DEF ImplBecomeReady, Predecessors, S!Next,
         S!BecomeReady, S!Predecessors

LEMMA StartRefines ==
    \A n \in Nodes : ImplStartRunning(n) => S!Next
  BY DEF ImplStartRunning, S!Next, S!StartRunning

LEMMA CompleteRefines ==
    \A n \in Nodes : ImplCompleteNode(n) => S!Next
  BY DEF ImplCompleteNode, S!Next, S!CompleteNode

LEMMA DoneRefines == ImplDoneStuttering => S!Next
  BY DEF ImplDoneStuttering, S!Next, S!DoneStuttering, S!AllCompleted, vars, S!vars

LEMMA NextRefines == [ImplNext]_vars => [S!Next]_(S!vars)
  <1> SUFFICES ASSUME [ImplNext]_vars PROVE [S!Next]_(S!vars) OBVIOUS
  <1>0. CASE UNCHANGED vars BY <1>0 DEF vars, S!vars
  <1>1. CASE \E n \in Nodes : ImplBecomeReady(n)
    BY <1>1, ReadyRefines
  <1>2. CASE \E n \in Nodes : ImplStartRunning(n)
    BY <1>2, StartRefines
  <1>3. CASE \E n \in Nodes : ImplCompleteNode(n)
    BY <1>3, CompleteRefines
  <1>4. CASE ImplDoneStuttering BY <1>4, DoneRefines
  <1> QED BY <1>0, <1>1, <1>2, <1>3, <1>4 DEF ImplNext

THEOREM RefinementThm == Spec => S!Spec
  BY InitRefines, NextRefines, PTL DEF Spec, S!Spec, S!vars
====

