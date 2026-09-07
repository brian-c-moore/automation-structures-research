---- MODULE TraversalEngineImplRefinesSpec_Proof ----
EXTENDS TraversalEngineImplRefinesSpec, TLAPS

LEMMA InitRefines == Init => T!Init BY DEF Init, T!Init
LEMMA NextRefines == [ImplNext]_vars => [T!Next]_(T!vars)
  <1> SUFFICES ASSUME [ImplNext]_vars PROVE [T!Next]_(T!vars) OBVIOUS
  <1>0. CASE UNCHANGED vars BY <1>0 DEF vars, T!vars
  <1>1. CASE \E n \in Nodes : ImplVisitNode(n)
    BY <1>1 DEF ImplVisitNode, ImplInvariant, NodeCost, NodeChildren,
                  T!Next, T!VisitNode, T!NodeCost, T!NodeChildren
  <1>2. CASE \E n \in Nodes : ImplSkip(n)
    BY <1>2 DEF ImplSkip, ImplInvariant, T!Next, T!Skip
  <1>3. CASE ImplTerminateOrRead
    BY <1>3 DEF ImplTerminateOrRead, vars, T!vars
  <1> QED BY <1>0, <1>1, <1>2, <1>3 DEF ImplNext

THEOREM RefinementThm == Spec => T!Spec
  BY InitRefines, NextRefines, PTL DEF Spec, T!Spec
THEOREM RefinementOriginal == Spec => Refinement
  BY RefinementThm DEF Refinement
====
