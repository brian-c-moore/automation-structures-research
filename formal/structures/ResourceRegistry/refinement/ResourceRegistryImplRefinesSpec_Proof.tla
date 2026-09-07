---- MODULE ResourceRegistryImplRefinesSpec_Proof ----
EXTENDS ResourceRegistryImplRefinesSpec, TLAPS

Inv == ImplInvariant

LEMMA InitInv == Init => Inv BY DEF Init, Inv

LEMMA NextInv == Inv /\ [ImplNext]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [ImplNext]_vars PROVE Inv' OBVIOUS
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF Inv, ImplInvariant, TypeInvariant, UniqueMapping, vars
  <1>1. CASE \E k \in Keys, v \in Values : ImplRegister(k, v)
    BY <1>1 DEF ImplRegister, Inv
  <1>2. CASE \E k \in Keys : ImplDeregister(k)
    BY <1>2 DEF ImplDeregister, Inv
  <1>3. CASE ImplReadOrReject
    BY <1>3 DEF ImplReadOrReject, Inv, ImplInvariant, TypeInvariant,
                  UniqueMapping, vars
  <1> QED BY <1>0, <1>1, <1>2, <1>3 DEF ImplNext

THEOREM InvariantSafety == Spec => []Inv
  BY InitInv, NextInv, PTL DEF Spec

LEMMA InitRefines == Init => R!Init BY DEF Init, R!Init

LEMMA NextRefines == [ImplNext]_vars => [R!Next]_(R!vars)
  <1> SUFFICES ASSUME [ImplNext]_vars PROVE [R!Next]_(R!vars) OBVIOUS
  <1>0. CASE UNCHANGED vars BY <1>0 DEF vars, R!vars
  <1>1. CASE \E k \in Keys, v \in Values : ImplRegister(k, v)
    BY <1>1 DEF ImplRegister, R!Next, R!Register
  <1>2. CASE \E k \in Keys : ImplDeregister(k)
    BY <1>2 DEF ImplDeregister, R!Next, R!Deregister
  <1>3. CASE ImplReadOrReject BY <1>3 DEF ImplReadOrReject, vars, R!vars
  <1> QED BY <1>0, <1>1, <1>2, <1>3 DEF ImplNext

THEOREM RefinementThm == Spec => R!Spec
  BY InitRefines, NextRefines, PTL DEF Spec, R!Spec

THEOREM RefinementOriginal == Spec => Refinement
  BY RefinementThm DEF Refinement
====
