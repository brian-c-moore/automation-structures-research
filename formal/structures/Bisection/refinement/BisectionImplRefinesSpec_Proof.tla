---- MODULE BisectionImplRefinesSpec_Proof ----
EXTENDS BisectionImplRefinesSpec, TLAPS

Inv == ImplInvariant
LEMMA InitInv == Init => Inv BY DEF Init, Inv
LEMMA NextInv == Inv /\ [ImplNext]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [ImplNext]_vars PROVE Inv' OBVIOUS
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF Inv, ImplInvariant, TypeInvariant, Monotonicity,
                  ProbeBound, WidthExpBound, vars
  <1>1. CASE ImplProbeLeft BY <1>1 DEF ImplProbeLeft, Inv
  <1>2. CASE ImplProbeRight BY <1>2 DEF ImplProbeRight, Inv
  <1>3. CASE ImplReadOrConverged
    BY <1>3 DEF ImplReadOrConverged, Inv, ImplInvariant,
                  TypeInvariant, Monotonicity, ProbeBound, WidthExpBound, vars
  <1> QED BY <1>0, <1>1, <1>2, <1>3 DEF ImplNext, ImplProgress

THEOREM InvariantSafety == Spec => []Inv BY InitInv, NextInv, PTL DEF Spec

LEMMA InitRefines == Init => B!Init BY DEF Init, B!Init
LEMMA NextRefines == [ImplNext]_vars => [B!Next]_(B!vars)
  <1> SUFFICES ASSUME [ImplNext]_vars PROVE [B!Next]_(B!vars) OBVIOUS
  <1>0. CASE UNCHANGED vars BY <1>0 DEF vars, B!vars
  <1>1. CASE ImplProbeLeft
    BY <1>1 DEF ImplProbeLeft, ImplInvariant, TypeInvariant,
                  Mid, B!Next, B!ProbeLeft, B!Mid, B!vars
  <1>2. CASE ImplProbeRight
    BY <1>2 DEF ImplProbeRight, ImplInvariant, TypeInvariant,
                  Mid, B!Next, B!ProbeRight, B!Mid, B!vars
  <1>3. CASE ImplReadOrConverged
    BY <1>3 DEF ImplReadOrConverged, vars, B!vars
  <1> QED BY <1>0, <1>1, <1>2, <1>3 DEF ImplNext, ImplProgress

THEOREM RefinementThm == Spec => B!Spec
  BY InitRefines, NextRefines, PTL
     DEF Spec, SchedulerFairnessRely, B!Spec, B!vars
THEOREM RefinementOriginal == Spec => Refinement
  BY RefinementThm DEF Refinement
====
