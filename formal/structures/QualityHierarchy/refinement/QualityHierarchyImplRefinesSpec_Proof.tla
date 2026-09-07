---- MODULE QualityHierarchyImplRefinesSpec_Proof ----
EXTENDS QualityHierarchyImplRefinesSpec, TLAPS

LEMMA InitRefines == Init => Q!Init BY DEF Init, Q!Init
LEMMA NextRefines == [ImplNext]_vars => [Q!Next]_(Q!vars)
  <1> SUFFICES ASSUME [ImplNext]_vars PROVE [Q!Next]_(Q!vars) OBVIOUS
  <1>0. CASE UNCHANGED vars BY <1>0 DEF vars, Q!vars
  <1>1. CASE \E p \in Nodes, c \in Nodes : ImplAddChild(p, c)
    BY <1>1 DEF ImplAddChild, ImplInvariant, Q!Next, Q!AddChild
  <1>2. CASE \E n \in Nodes, l \in 0..MaxLevel, c \in 0..MaxLevel :
                  ImplSetNodeProperties(n, l, c)
    BY <1>2 DEF ImplSetNodeProperties, ImplInvariant,
                  Q!Next, Q!SetNodeProperties
  <1>3. CASE ImplReadOrReject BY <1>3 DEF ImplReadOrReject, vars, Q!vars
  <1> QED BY <1>0, <1>1, <1>2, <1>3 DEF ImplNext

THEOREM RefinementThm == Spec => Q!Spec
  BY InitRefines, NextRefines, PTL DEF Spec, Q!Spec
THEOREM RefinementOriginal == Spec => Refinement
  BY RefinementThm DEF Refinement
====
