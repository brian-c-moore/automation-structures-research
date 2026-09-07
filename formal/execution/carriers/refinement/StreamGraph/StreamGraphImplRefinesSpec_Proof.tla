---- MODULE StreamGraphImplRefinesSpec_Proof ----
EXTENDS StreamGraphImplRefinesSpec, TLAPS

LEMMA InitRefines == Init => G!Init BY DEF Init, G!Init

LEMMA NextRefines == [ImplNext]_vars => [G!Next]_(G!vars)
  <1> SUFFICES ASSUME [ImplNext]_vars PROVE [G!Next]_(G!vars) OBVIOUS
  <1>0. CASE UNCHANGED vars BY <1>0 DEF vars, G!vars
  <1>1. CASE \E v \in RecordDomain : ImplSourceIngest(v)
    BY <1>1 DEF ImplSourceIngest, IsFull, G!Next, G!SourceIngest, G!IsFull, G!vars
  <1>2. CASE ImplMiddle2Fire
    BY <1>2 DEF ImplMiddle2Fire, IsFull, IsEmpty,
                  G!Next, G!Middle2Fire, G!IsFull, G!IsEmpty, G!vars
  <1>3. CASE ImplMiddle3Fire
    BY <1>3 DEF ImplMiddle3Fire, IsFull, IsEmpty,
                  G!Next, G!Middle3Fire, G!IsFull, G!IsEmpty, G!vars
  <1>4. CASE ImplSinkConsume3
    BY <1>4 DEF ImplSinkConsume3, IsEmpty,
                  G!Next, G!SinkConsume3, G!IsEmpty, G!vars
  <1>5. CASE ImplSinkConsume4
    BY <1>5 DEF ImplSinkConsume4, IsEmpty,
                  G!Next, G!SinkConsume4, G!IsEmpty, G!vars
  <1>6. CASE ImplDoneStuttering
    BY <1>6 DEF ImplDoneStuttering, vars, G!vars
  <1> QED BY <1>0, <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF ImplNext

THEOREM RefinementThm == Spec => G!Spec
  BY InitRefines, NextRefines, PTL DEF Spec, G!Spec, G!vars
====
