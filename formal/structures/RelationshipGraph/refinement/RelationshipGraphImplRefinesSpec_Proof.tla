---- MODULE RelationshipGraphImplRefinesSpec_Proof ----
EXTENDS RelationshipGraphImplRefinesSpec, TLAPS

LEMMA InitRefines == Init => G!Init BY DEF Init, G!Init
LEMMA NextRefines == [ImplNext]_vars => [G!Next]_(G!vars)
  <1> SUFFICES ASSUME [ImplNext]_vars PROVE [G!Next]_(G!vars) OBVIOUS
  <1>0. CASE UNCHANGED vars BY <1>0 DEF vars, G!vars
  <1>1. CASE \E s \in Nodes, d \in Nodes, w \in 0..MaxWeight : ImplAddEdge(s, d, w)
    BY <1>1 DEF ImplAddEdge, ImplInvariant, G!Next, G!AddEdge
  <1>2. CASE \E s \in Nodes, d \in Nodes : ImplRemoveEdge(s, d)
    BY <1>2 DEF ImplRemoveEdge, ImplInvariant, G!Next, G!RemoveEdge
  <1>3. CASE ImplReadOrReject BY <1>3 DEF ImplReadOrReject, vars, G!vars
  <1> QED BY <1>0, <1>1, <1>2, <1>3 DEF ImplNext

THEOREM RefinementThm == Spec => G!Spec
  BY InitRefines, NextRefines, PTL DEF Spec, G!Spec
THEOREM RefinementOriginal == Spec => Refinement
  BY RefinementThm DEF Refinement
====
