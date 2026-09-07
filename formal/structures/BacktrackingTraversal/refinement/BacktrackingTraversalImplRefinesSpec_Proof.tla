---- MODULE BacktrackingTraversalImplRefinesSpec_Proof ----
EXTENDS BacktrackingTraversalImplRefinesSpec, TLAPS

Inv == ImplInvariant
LEMMA InitInv == Init => Inv BY DEF Init, Inv
LEMMA NextInv == Inv /\ [ImplNext]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [ImplNext]_vars PROVE Inv' OBVIOUS
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF Inv, ImplInvariant, B!TypeInvariant, B!Pairing,
                  B!StateRestoration, B!RecordedLeafValidity, B!Depth, vars
  <1>1. CASE \E c \in 1..BranchFactor, d \in DeltaSet : ImplDescend(c, d)
    BY <1>1 DEF ImplDescend, Inv
  <1>2. CASE ImplVisit BY <1>2 DEF ImplVisit, Inv
  <1>3. CASE ImplAscend BY <1>3 DEF ImplAscend, Inv
  <1>4. CASE ImplReadOrReject
    BY <1>4 DEF ImplReadOrReject, Inv, ImplInvariant, B!TypeInvariant,
                  B!Pairing, B!StateRestoration, B!RecordedLeafValidity,
                  B!Depth, vars
  <1> QED BY <1>0, <1>1, <1>2, <1>3, <1>4 DEF ImplNext

THEOREM InvariantSafety == Spec => []Inv BY InitInv, NextInv, PTL DEF Spec

LEMMA InitRefines == Init => B!Init BY DEF Init, B!Init
LEMMA NextRefines == [ImplNext]_vars => [B!Next]_(B!vars)
  <1> SUFFICES ASSUME [ImplNext]_vars PROVE [B!Next]_(B!vars) OBVIOUS
  <1>0. CASE UNCHANGED vars BY <1>0 DEF vars, B!vars
  <1>1. CASE \E c \in 1..BranchFactor, d \in DeltaSet : ImplDescend(c, d)
    BY <1>1 DEF ImplDescend, ImplInvariant, B!Next, B!Descend,
                  B!IsLeaf, B!Depth, B!vars
  <1>2. CASE ImplVisit
    BY <1>2 DEF ImplVisit, ImplInvariant, B!Next, B!Visit,
                  B!IsLeaf, B!Depth, B!vars
  <1>3. CASE ImplAscend
    BY <1>3 DEF ImplAscend, ImplInvariant, B!Next, B!Ascend,
                  B!Depth, B!vars
  <1>4. CASE ImplReadOrReject BY <1>4 DEF ImplReadOrReject, vars, B!vars
  <1> QED BY <1>0, <1>1, <1>2, <1>3, <1>4 DEF ImplNext

THEOREM RefinementThm == Spec => B!Spec
  BY InitRefines, NextRefines, PTL DEF Spec, B!Spec
THEOREM RefinementOriginal == Spec => Refinement
  BY RefinementThm DEF Refinement
====
