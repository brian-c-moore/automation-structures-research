---- MODULE FederatedBudgetFromBudgets_Proof ----
(***************************************************************************
  Parametric refinement proof for the paired-Budget construction.

  Refinement establishes Spec => FB!Spec. TypeSafety and the two Budget
  preservation theorems establish the construction invariants independently.
  SubPoolNames may be empty, finite, or infinite because this construction
  uses no cardinality or sum; MasterCapacity is assumed to be a natural.
 ***************************************************************************)
EXTENDS FederatedBudgetFromBudgets, TLAPS

ASSUME MasterCapacityAss == MasterCapacity \in Nat

\* Each sub-pool ledger is bounded by the master allocation. This sum-free
\* coupling is sufficient for every instantiated Budget safety invariant and
\* remains meaningful for arbitrary SubPoolNames.
SubCeiling ==
    \A n \in SubPoolNames :
        sub_alloc[n] + sub_res[n] + sub_pend[n] <= m_allocated

Inv == TypeInvariant /\ SubCeiling

(*-------------------------------------------------------------------------*)
(* Lemma: Init establishes the inductive invariant.                        *)
(*-------------------------------------------------------------------------*)
LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv
    OBVIOUS
  <1>1. TypeInvariant
    BY MasterCapacityAss DEF Init, TypeInvariant
  <1>2. SubCeiling
    BY DEF Init, SubCeiling
  <1> QED BY <1>1, <1>2 DEF Inv

(*-------------------------------------------------------------------------*)
(* Lemma: every Next step preserves the inductive invariant.               *)
(*-------------------------------------------------------------------------*)
LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <1>c. /\ m_capacity = MasterCapacity
        /\ m_allocated \in 0..MasterCapacity
        /\ m_reserved = 0
        /\ m_pending = 0
        /\ sub_alloc \in [SubPoolNames -> Nat]
        /\ sub_res \in [SubPoolNames -> Nat]
        /\ sub_pend = [n \in SubPoolNames |-> 0]
        /\ SubCeiling
    BY DEF Inv, TypeInvariant
  <1>0. CASE UNCHANGED vars
    BY <1>0, <1>c DEF Inv, vars, TypeInvariant, SubCeiling
  <1>1. CASE \E name \in SubPoolNames, a \in 1..MasterCapacity :
                CarveSubPool(name, a)
    <2> SUFFICES ASSUME NEW name \in SubPoolNames,
                        NEW a \in 1..MasterCapacity, CarveSubPool(name, a)
                 PROVE Inv'
      BY <1>1
    <2>a. /\ m_allocated + m_reserved + m_pending + a <= m_capacity
          /\ m_allocated' = m_allocated + a
          /\ sub_res' = [sub_res EXCEPT ![name] = @ + a]
          /\ UNCHANGED <<m_capacity, m_reserved, m_pending,
                         sub_alloc, sub_pend>>
      BY DEF CarveSubPool
    <2>t. a \in Nat /\ m_allocated \in Nat /\ sub_res[name] \in Nat
      BY <1>c, MasterCapacityAss
    <2>1. m_allocated' \in 0..MasterCapacity
      BY <2>a, <2>t, <1>c, MasterCapacityAss
    <2>2. sub_res' \in [SubPoolNames -> Nat]
      BY <2>a, <2>t, <1>c
    <2>3. SubCeiling'
      <3> SUFFICES ASSUME NEW n \in SubPoolNames
                   PROVE  sub_alloc'[n] + sub_res'[n] + sub_pend'[n]
                              <= m_allocated'
        BY DEF SubCeiling
      <3>1. sub_alloc[n] + sub_res[n] + sub_pend[n] <= m_allocated
        BY <1>c DEF SubCeiling
      <3> QED BY <3>1, <2>a, <2>t, <1>c
    <2> QED BY <2>a, <2>1, <2>2, <2>3, <1>c DEF Inv, TypeInvariant
  <1>2. CASE \E name \in SubPoolNames, a \in 1..MasterCapacity :
                ConsumeFromSubPool(name, a)
    <2> SUFFICES ASSUME NEW name \in SubPoolNames,
                        NEW a \in 1..MasterCapacity, ConsumeFromSubPool(name, a)
                 PROVE Inv'
      BY <1>2
    <2>a. /\ a <= sub_res[name]
          /\ sub_alloc' = [sub_alloc EXCEPT ![name] = @ + a]
          /\ sub_res' = [sub_res EXCEPT ![name] = @ - a]
          /\ UNCHANGED <<m_capacity, m_allocated, m_reserved, m_pending,
                         sub_pend>>
      BY DEF ConsumeFromSubPool
    <2>t. a \in Nat /\ sub_alloc[name] \in Nat /\ sub_res[name] \in Nat
      BY <1>c, MasterCapacityAss
    <2>1. sub_alloc' \in [SubPoolNames -> Nat]
      BY <2>a, <2>t, <1>c
    <2>2. sub_res' \in [SubPoolNames -> Nat]
      BY <2>a, <2>t, <1>c
    <2>3. SubCeiling'
      <3> SUFFICES ASSUME NEW n \in SubPoolNames
                   PROVE  sub_alloc'[n] + sub_res'[n] + sub_pend'[n]
                              <= m_allocated'
        BY DEF SubCeiling
      <3>1. sub_alloc[n] + sub_res[n] + sub_pend[n] <= m_allocated
        BY <1>c DEF SubCeiling
      <3> QED BY <3>1, <2>a, <2>t, <1>c
    <2> QED BY <2>a, <2>1, <2>2, <2>3, <1>c DEF Inv, TypeInvariant
  <1>3. CASE \E name \in SubPoolNames, a \in 1..MasterCapacity :
                ReleaseFromSubPool(name, a)
    <2> SUFFICES ASSUME NEW name \in SubPoolNames,
                        NEW a \in 1..MasterCapacity, ReleaseFromSubPool(name, a)
                 PROVE Inv'
      BY <1>3
    <2>a. /\ a <= sub_alloc[name]
          /\ sub_alloc' = [sub_alloc EXCEPT ![name] = @ - a]
          /\ sub_res' = [sub_res EXCEPT ![name] = @ + a]
          /\ UNCHANGED <<m_capacity, m_allocated, m_reserved, m_pending,
                         sub_pend>>
      BY DEF ReleaseFromSubPool
    <2>t. a \in Nat /\ sub_alloc[name] \in Nat /\ sub_res[name] \in Nat
      BY <1>c, MasterCapacityAss
    <2>1. sub_alloc' \in [SubPoolNames -> Nat]
      BY <2>a, <2>t, <1>c
    <2>2. sub_res' \in [SubPoolNames -> Nat]
      BY <2>a, <2>t, <1>c
    <2>3. SubCeiling'
      <3> SUFFICES ASSUME NEW n \in SubPoolNames
                   PROVE  sub_alloc'[n] + sub_res'[n] + sub_pend'[n]
                              <= m_allocated'
        BY DEF SubCeiling
      <3>1. sub_alloc[n] + sub_res[n] + sub_pend[n] <= m_allocated
        BY <1>c DEF SubCeiling
      <3> QED BY <3>1, <2>a, <2>t, <1>c
    <2> QED BY <2>a, <2>1, <2>2, <2>3, <1>c DEF Inv, TypeInvariant
  <1> QED BY <1>0, <1>1, <1>2, <1>3 DEF Next

(*-------------------------------------------------------------------------*)
(* Safety: the inductive invariant holds in every reachable state.         *)
(*-------------------------------------------------------------------------*)
THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv
    BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'
    BY NextInv
  <1> QED BY <1>1, <1>2, PTL DEF Spec

THEOREM TypeSafety == Spec => []TypeInvariant
  BY Safety, PTL DEF Inv

THEOREM MasterBudgetSafetyPreservation == Spec => []MasterBudgetSafety
  <1>1. Inv => MasterBudgetSafety
    BY MasterCapacityAss
       DEF Inv, TypeInvariant, MasterBudgetSafety, Master!SafetyInvariant
  <1> QED BY Safety, <1>1, PTL

THEOREM SubBudgetSafetyPreservation == Spec => []SubBudgetSafety
  <1>1. Inv => SubBudgetSafety
    <2> SUFFICES ASSUME Inv, NEW n \in SubPoolNames
                 PROVE  sub_alloc[n] + sub_res[n] + sub_pend[n] <= MasterCapacity
      BY DEF SubBudgetSafety, Sub!SafetyInvariant
    <2>1. sub_alloc[n] + sub_res[n] + sub_pend[n] <= m_allocated
      BY DEF Inv, SubCeiling
    <2>2. m_allocated <= MasterCapacity
      BY MasterCapacityAss DEF Inv, TypeInvariant
    <2> QED BY <2>1, <2>2, MasterCapacityAss DEF Inv, TypeInvariant
  <1> QED BY Safety, <1>1, PTL

(*-------------------------------------------------------------------------*)
(* The refinement: Init maps to FB!Init, every step maps to an FB step or  *)
(* an FB stutter.                                                          *)
(*-------------------------------------------------------------------------*)
LEMMA InitRefines == Init => FB!Init
  <1> SUFFICES ASSUME Init PROVE FB!Init
    OBVIOUS
  <1>1. m_allocated = 0
    BY DEF Init
  <1>2. MapSubCapacities = [n \in SubPoolNames |-> 0]
    BY DEF Init, MapSubCapacities
  <1>3. sub_alloc = [n \in SubPoolNames |-> 0]
    BY DEF Init
  <1> QED BY <1>1, <1>2, <1>3 DEF FB!Init

LEMMA NextRefines == Inv /\ [Next]_vars => [FB!Next]_(FB!vars)
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE [FB!Next]_(FB!vars)
    OBVIOUS
  <1>c. /\ m_capacity = MasterCapacity
        /\ m_allocated \in 0..MasterCapacity
        /\ m_reserved = 0
        /\ m_pending = 0
        /\ sub_alloc \in [SubPoolNames -> Nat]
        /\ sub_res \in [SubPoolNames -> Nat]
        /\ sub_pend = [n \in SubPoolNames |-> 0]
    BY DEF Inv, TypeInvariant
  <1>0. CASE UNCHANGED vars
    <2>1. UNCHANGED <<m_allocated, MapSubCapacities, sub_alloc>>
      BY <1>0 DEF vars, MapSubCapacities
    <2> QED BY <2>1 DEF FB!vars
  <1>1. CASE \E name \in SubPoolNames, a \in 1..MasterCapacity :
                CarveSubPool(name, a)
    <2> SUFFICES ASSUME NEW name \in SubPoolNames,
                        NEW a \in 1..MasterCapacity, CarveSubPool(name, a)
                 PROVE  [FB!Next]_(FB!vars)
      BY <1>1
    <2>a. /\ m_allocated + m_reserved + m_pending + a <= m_capacity
          /\ m_allocated' = m_allocated + a
          /\ sub_res' = [sub_res EXCEPT ![name] = @ + a]
          /\ UNCHANGED <<m_capacity, m_reserved, m_pending,
                         sub_alloc, sub_pend>>
      BY DEF CarveSubPool
    <2>t. a \in Nat /\ m_allocated \in Nat
      BY <1>c, MasterCapacityAss
    <2>1. m_allocated + a <= MasterCapacity
      BY <2>a, <2>t, <1>c
    <2>2. MapSubCapacities' = [MapSubCapacities EXCEPT ![name] = @ + a]
      <3>1. \A n \in SubPoolNames :
                sub_alloc'[n] + sub_res'[n] =
                    IF n = name THEN (sub_alloc[n] + sub_res[n]) + a
                                ELSE sub_alloc[n] + sub_res[n]
        BY <2>a, <1>c, <2>t
      <3> QED BY <3>1 DEF MapSubCapacities
    <2>3. FB!AllocateSubPool(name, a)
      BY <2>a, <2>1, <2>2 DEF FB!AllocateSubPool
    <2> QED BY <2>3 DEF FB!Next
  <1>2. CASE \E name \in SubPoolNames, a \in 1..MasterCapacity :
                ConsumeFromSubPool(name, a)
    <2> SUFFICES ASSUME NEW name \in SubPoolNames,
                        NEW a \in 1..MasterCapacity, ConsumeFromSubPool(name, a)
                 PROVE  [FB!Next]_(FB!vars)
      BY <1>2
    <2>a. /\ a <= sub_res[name]
          /\ sub_alloc' = [sub_alloc EXCEPT ![name] = @ + a]
          /\ sub_res' = [sub_res EXCEPT ![name] = @ - a]
          /\ UNCHANGED <<m_capacity, m_allocated, m_reserved, m_pending,
                         sub_pend>>
      BY DEF ConsumeFromSubPool
    <2>t. a \in Nat /\ sub_alloc[name] \in Nat /\ sub_res[name] \in Nat
      BY <1>c, MasterCapacityAss
    <2>1. sub_alloc[name] + a <= MapSubCapacities[name]
      BY <2>a, <2>t DEF MapSubCapacities
    <2>2. MapSubCapacities' = MapSubCapacities
      <3>1. \A n \in SubPoolNames :
                sub_alloc'[n] + sub_res'[n] = sub_alloc[n] + sub_res[n]
        BY <2>a, <1>c, <2>t
      <3> QED BY <3>1 DEF MapSubCapacities
    <2>3. sub_alloc' = [sub_alloc EXCEPT ![name] = @ + a]
      BY <2>a
    <2>4. FB!AllocateFromSubPool(name, a)
      BY <2>a, <2>1, <2>2, <2>3 DEF FB!AllocateFromSubPool, MapSubCapacities
    <2> QED BY <2>4 DEF FB!Next
  <1>3. CASE \E name \in SubPoolNames, a \in 1..MasterCapacity :
                ReleaseFromSubPool(name, a)
    <2> SUFFICES ASSUME NEW name \in SubPoolNames,
                        NEW a \in 1..MasterCapacity, ReleaseFromSubPool(name, a)
                 PROVE  [FB!Next]_(FB!vars)
      BY <1>3
    <2>a. /\ a <= sub_alloc[name]
          /\ sub_alloc' = [sub_alloc EXCEPT ![name] = @ - a]
          /\ sub_res' = [sub_res EXCEPT ![name] = @ + a]
          /\ UNCHANGED <<m_capacity, m_allocated, m_reserved, m_pending,
                         sub_pend>>
      BY DEF ReleaseFromSubPool
    <2>t. a \in Nat /\ sub_alloc[name] \in Nat /\ sub_res[name] \in Nat
      BY <1>c, MasterCapacityAss
    <2>2. MapSubCapacities' = MapSubCapacities
      <3>1. \A n \in SubPoolNames :
                sub_alloc'[n] + sub_res'[n] = sub_alloc[n] + sub_res[n]
        BY <2>a, <1>c, <2>t
      <3> QED BY <3>1 DEF MapSubCapacities
    <2>3. FB!ReleaseFromSubPool(name, a)
      BY <2>a, <2>2 DEF FB!ReleaseFromSubPool
    <2> QED BY <2>3 DEF FB!Next
  <1> QED BY <1>0, <1>1, <1>2, <1>3 DEF Next

(*-------------------------------------------------------------------------*)
(* The main result: the construction refines FederatedBudget, unbounded.   *)
(* Discharges the base module's Spec => FBRefinement claim.                *)
(*-------------------------------------------------------------------------*)
THEOREM Refinement == Spec => FB!Spec
  <1>1. Init => FB!Init
    BY InitRefines
  <1>2. Inv /\ [Next]_vars => [FB!Next]_(FB!vars)
    BY NextRefines
  <1>3. Spec => []Inv
    BY Safety
  <1> QED BY <1>1, <1>2, <1>3, PTL DEF Spec, FB!Spec

\* Restatement in the base module's own vocabulary.
THEOREM RefinementOriginal == Spec => FBRefinement
  BY Refinement DEF FBRefinement

====
