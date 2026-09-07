---- MODULE ConvergenceGovernorImplRefinesSpec_Proof ----
EXTENDS ConvergenceGovernorImplRefinesSpec, TLAPS

Inv == ImplInvariant
LEMMA InitInv == Init => Inv BY DEF Init, Inv
LEMMA NextInv == Inv /\ [ImplNext]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [ImplNext]_vars PROVE Inv' OBVIOUS
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF Inv, ImplInvariant, TypeInvariant, PeakImplies,
                  NoCoolingFromCold, ConvergenceRequiresHistory, vars
  <1>1. CASE \E d \in 0..MaxDelta : ImplUpdate(d)
    BY <1>1 DEF ImplUpdate, Inv
  <1>2. CASE ImplRead
    BY <1>2 DEF ImplRead, Inv, ImplInvariant, TypeInvariant, PeakImplies,
                  NoCoolingFromCold, ConvergenceRequiresHistory, vars
  <1> QED BY <1>0, <1>1, <1>2 DEF ImplNext

THEOREM InvariantSafety == Spec => []Inv BY InitInv, NextInv, PTL DEF Spec

LEMMA InitRefines == Init => C!Init BY DEF Init, C!Init
LEMMA NextRefines == [ImplNext]_vars => [C!Next]_(C!vars)
  <1> SUFFICES ASSUME [ImplNext]_vars PROVE [C!Next]_(C!vars) OBVIOUS
  <1>0. CASE UNCHANGED vars BY <1>0 DEF vars, C!vars
  <1>1. CASE \E d \in 0..MaxDelta : ImplUpdate(d)
    BY <1>1 DEF ImplUpdate, ImplInvariant, TypeInvariant, NewHistory,
                  NewAverage, Classify, NextState, SumSeq, Max,
                  C!Next, C!Update, C!ClassifyPhase, C!SumSeq, C!Max
  <1>2. CASE ImplRead BY <1>2 DEF ImplRead, vars, C!vars
  <1> QED BY <1>0, <1>1, <1>2 DEF ImplNext

THEOREM RefinementThm == Spec => C!Spec
  BY InitRefines, NextRefines, PTL DEF Spec, C!Spec
THEOREM RefinementOriginal == Spec => Refinement
  BY RefinementThm DEF Refinement
====
