---- MODULE ForkJoinImplRefinesSpec_Proof ----
EXTENDS ForkJoinImplRefinesSpec, TLAPS

LEMMA InitRefines == Init => F!Init BY DEF Init, F!Init

LEMMA StartRefines ==
    \A w \in Workers : ImplStartWorker(w) => F!Next
  BY DEF ImplStartWorker, F!Next, F!StartWorker

LEMMA CompleteRefines ==
    \A w \in Workers, v \in ValueDomain : ImplCompleteWorker(w, v) => F!Next
  BY DEF ImplCompleteWorker, F!Next, F!CompleteWorker

LEMMA BarrierRefines == ImplBarrier => F!Next
  BY DEF ImplBarrier, AllComplete, F!Next, F!Barrier, F!AllComplete

LEMMA OutputRefines == ImplProduceOutput => F!Next
  BY DEF ImplProduceOutput, F!Next, F!ProduceOutput

LEMMA DoneRefines == ImplDoneStuttering => F!Next
  BY DEF ImplDoneStuttering, F!Next, F!DoneStuttering, vars, F!vars

LEMMA NextRefines == [ImplNext]_vars => [F!Next]_(F!vars)
  <1> SUFFICES ASSUME [ImplNext]_vars PROVE [F!Next]_(F!vars) OBVIOUS
  <1>0. CASE UNCHANGED vars BY <1>0 DEF vars, F!vars
  <1>1. CASE \E w \in Workers : ImplStartWorker(w)
    BY <1>1, StartRefines
  <1>2. CASE \E w \in Workers, v \in ValueDomain : ImplCompleteWorker(w, v)
    BY <1>2, CompleteRefines
  <1>3. CASE ImplBarrier BY <1>3, BarrierRefines
  <1>4. CASE ImplProduceOutput BY <1>4, OutputRefines
  <1>5. CASE ImplDoneStuttering BY <1>5, DoneRefines
  <1> QED BY <1>0, <1>1, <1>2, <1>3, <1>4, <1>5 DEF ImplNext

THEOREM RefinementThm == Spec => F!Spec
  BY InitRefines, NextRefines, PTL DEF Spec, F!Spec, F!vars
====

