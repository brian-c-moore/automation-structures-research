---- MODULE ActuationPassImplRefinesSpec_Proof ----
(***************************************************************************)
(* Parametric proof for the transition relation transcribed from the Verus *)
(* ActuationPass contracts. No TLC finiteness assumption is used here.      *)
(***************************************************************************)
EXTENDS ActuationPassImplRefinesSpec, TLAPS

Inv == ImplInvariant

LEMMA InitInv == Init => Inv
  BY DEF Init, Inv

LEMMA NextInv == Inv /\ [ImplNext]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [ImplNext]_vars PROVE Inv' OBVIOUS
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF Inv, ImplInvariant, TypeInvariant, EffectFidelity,
                  PassCompleteness, ReadyToFinish, vars
  <1>1. CASE \E s \in Seats, r \in ResourceDomain : ImplAllocate(s, r)
    BY <1>1 DEF ImplAllocate, Inv
  <1>2. CASE \E s \in Seats : ImplDeallocate(s)
    BY <1>2 DEF ImplDeallocate, Inv
  <1>3. CASE \E s \in Seats : ImplActuate(s)
    BY <1>3 DEF ImplActuate, Inv
  <1>4. CASE ImplFinish
    BY <1>4 DEF ImplFinish, Inv
  <1>5. CASE ImplReadOrReject
    BY <1>5 DEF ImplReadOrReject, Inv, ImplInvariant, TypeInvariant,
                  EffectFidelity, PassCompleteness,
                  ReadyToFinish, vars
  <1> QED BY <1>0, <1>1, <1>2, <1>3, <1>4, <1>5 DEF ImplNext

THEOREM InvariantSafety == Spec => []Inv
  <1>1. Init => Inv BY InitInv
  <1>2. Inv /\ [ImplNext]_vars => Inv' BY NextInv
  <1> QED BY <1>1, <1>2, PTL DEF Spec

LEMMA InitRefines == Init => A!Init
  BY DEF Init, A!Init

LEMMA NextRefines == [ImplNext]_vars => [A!Next]_(A!vars)
  <1> SUFFICES ASSUME [ImplNext]_vars PROVE [A!Next]_(A!vars) OBVIOUS
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF vars, A!vars
  <1>1. CASE \E s \in Seats, r \in ResourceDomain : ImplAllocate(s, r)
    BY <1>1 DEF ImplAllocate, A!Next, A!Allocate
  <1>2. CASE \E s \in Seats : ImplDeallocate(s)
    BY <1>2 DEF ImplDeallocate, A!Next, A!Deallocate
  <1>3. CASE \E s \in Seats : ImplActuate(s)
    BY <1>3 DEF ImplActuate, A!Next, A!Actuate
  <1>4. CASE ImplFinish
    BY <1>4 DEF ImplFinish, ReadyToFinish, A!Next, A!Finish
  <1>5. CASE ImplReadOrReject
    BY <1>5 DEF ImplReadOrReject, vars, A!vars
  <1> QED BY <1>0, <1>1, <1>2, <1>3, <1>4, <1>5 DEF ImplNext

THEOREM RefinementThm == Spec => A!Spec
  <1>1. Init => A!Init BY InitRefines
  <1>2. [ImplNext]_vars => [A!Next]_(A!vars) BY NextRefines
  <1> QED BY <1>1, <1>2, PTL DEF Spec, A!Spec

THEOREM RefinementOriginal == Spec => Refinement
  BY RefinementThm DEF Refinement
====
