---- MODULE Budget_Proof ----
(* TLAPS proof of Budget's safety obligation: the four-term ledger inequality
   holds in every reachable state, unbounded in Capacity. *)
EXTENDS Budget, Naturals, TLAPS

ASSUME CapacityType == Capacity \in Nat

Inv == TypeInvariant /\ SafetyInvariant

LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv  OBVIOUS
  <1>1. TypeInvariant     BY CapacityType DEF Init, TypeInvariant
  <1>2. SafetyInvariant   BY CapacityType DEF Init, SafetyInvariant
  <1> QED  BY <1>1, <1>2 DEF Inv

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'  OBVIOUS
  <1> USE DEF Inv, TypeInvariant, SafetyInvariant
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF vars
  <1>A. CASE \E a \in 1..capacity : TryAllocate(a)
    <2> SUFFICES ASSUME NEW a \in 1..capacity, TryAllocate(a) PROVE Inv'
      BY <1>A
    <2>1. CASE allocated + reserved + pending_eviction + a <= capacity
      BY <2>1 DEF TryAllocate
    <2>2. CASE ~(allocated + reserved + pending_eviction + a <= capacity)
      BY <2>2 DEF TryAllocate, vars
    <2> QED  BY <2>1, <2>2
  <1>B. CASE \E a \in 1..capacity : Reserve(a)
    <2> SUFFICES ASSUME NEW a \in 1..capacity, Reserve(a) PROVE Inv'
      BY <1>B
    <2>1. CASE allocated + reserved + pending_eviction + a <= capacity
      BY <2>1 DEF Reserve
    <2>2. CASE ~(allocated + reserved + pending_eviction + a <= capacity)
      BY <2>2 DEF Reserve, vars
    <2> QED  BY <2>1, <2>2
  <1>C. CASE \E a \in 1..reserved : CommitReservation(a)
    <2> SUFFICES ASSUME NEW a \in 1..reserved, CommitReservation(a) PROVE Inv'
      BY <1>C
    <2> QED  BY DEF CommitReservation
  <1>D. CASE \E a \in 1..allocated : Release(a)
    <2> SUFFICES ASSUME NEW a \in 1..allocated, Release(a) PROVE Inv'
      BY <1>D
    <2> QED  BY DEF Release
  <1>E. CASE \E a \in 1..allocated : MarkEviction(a)
    <2> SUFFICES ASSUME NEW a \in 1..allocated, MarkEviction(a) PROVE Inv'
      BY <1>E
    <2> QED  BY DEF MarkEviction
  <1>F. CASE \E a \in 1..pending_eviction : CompleteEviction(a)
    <2> SUFFICES ASSUME NEW a \in 1..pending_eviction, CompleteEviction(a) PROVE Inv'
      BY <1>F
    <2> QED  BY DEF CompleteEviction
  <1>X. CASE Next
    BY <1>X, <1>A, <1>B, <1>C, <1>D, <1>E, <1>F DEF Next
  <1> QED  BY <1>0, <1>X

THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv               BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'  BY NextInv
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

THEOREM TypeSafety == Spec => []TypeInvariant         BY Safety, PTL DEF Inv
THEOREM SafetyInvariantSafety == Spec => []SafetyInvariant  BY Safety, PTL DEF Inv
====
