---- MODULE PropagationPassImplRefinesSpec_Proof ----
EXTENDS PropagationPassImplRefinesSpec, TLAPS

Inv == ImplInvariant
LEMMA InitInv == Init => Inv BY DEF Init, Inv

LEMMA NextInv == Inv /\ [ImplNext]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [ImplNext]_vars PROVE Inv' OBVIOUS
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF Inv, ImplInvariant, TypeInvariant, IterationBound,
                  SnapshotLocality, RoundBound, RunningChanged, SettledOk,
                  AllUpdated, vars
  <1>1. CASE ImplStartRound BY <1>1 DEF ImplStartRound, Inv
  <1>2. CASE \E n \in Nodes : ImplUpdateNode(n)
    BY <1>2 DEF ImplUpdateNode, Inv
  <1>3. CASE ImplEndRound BY <1>3 DEF ImplEndRound, Inv
  <1>4. CASE ImplTerminateOrRead
    BY <1>4 DEF ImplTerminateOrRead, Inv, ImplInvariant, TypeInvariant,
                  IterationBound, SnapshotLocality, RoundBound,
                  RunningChanged, SettledOk, AllUpdated, vars
  <1> QED BY <1>0, <1>1, <1>2, <1>3, <1>4 DEF ImplNext

THEOREM InvariantSafety == Spec => []Inv
  BY InitInv, NextInv, PTL DEF Spec

LEMMA InitRefines == Init => P!Init BY DEF Init, P!Init

LEMMA NextRefines == [ImplNext]_vars => [P!Next]_(P!vars)
  <1> SUFFICES ASSUME [ImplNext]_vars PROVE [P!Next]_(P!vars) OBVIOUS
  <1>0. CASE UNCHANGED vars BY <1>0 DEF vars, P!vars
  <1>1. CASE ImplStartRound
    BY <1>1 DEF ImplStartRound, ImplInvariant, TypeInvariant,
                  P!Next, P!StartRound
  <1>2. CASE \E n \in Nodes : ImplUpdateNode(n)
    BY <1>2 DEF ImplUpdateNode, Combine, InNbr,
                  P!Combine, P!InNbr, P!Next, P!UpdateNode
  <1>3. CASE ImplEndRound
    BY <1>3 DEF ImplEndRound, AllUpdated, P!Next, P!EndRound
  <1>4. CASE ImplTerminateOrRead
    BY <1>4 DEF ImplTerminateOrRead, vars, P!vars
  <1> QED BY <1>0, <1>1, <1>2, <1>3, <1>4 DEF ImplNext

THEOREM RefinementThm == Spec => P!Spec
  BY InitRefines, NextRefines, PTL
     DEF Spec, SchedulerFairnessRely, P!Spec

THEOREM RefinementOriginal == Spec => Refinement
  BY RefinementThm DEF Refinement
====
