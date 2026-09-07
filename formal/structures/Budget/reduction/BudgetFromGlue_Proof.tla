---- MODULE BudgetFromGlue_Proof ----
(***************************************************************************
  Parametric TLAPS proof of the Budget pure-glue refinement:

      Refinement == Spec => BGT!Spec

  Under the substitution, Init, Next, and vars are the Budget target with
  renamed variables, so refinement is definitional. Capacity typing is used
  only for the construction TypeInvariant. The theorem does not show that a
  retained component supplies SafetyInvariant; all obligation-bearing state
  remains glue.
 ***************************************************************************)
EXTENDS BudgetFromGlue, TLAPS

ASSUME CapacityType == Capacity \in Nat

Inv == TypeInvariant

(*-------------------------------------------------------------------------*)
(* Safety of the construction's own (type) invariant.                      *)
(*-------------------------------------------------------------------------*)
LEMMA InitInv == Init => Inv
  BY CapacityType DEF Init, Inv, TypeInvariant

LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'  OBVIOUS
  <1> USE DEF Inv, TypeInvariant
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF vars
  <1>A. CASE \E a \in 1..c_capacity : TryAllocate(a)
    <2> SUFFICES ASSUME NEW a \in 1..c_capacity, TryAllocate(a) PROVE Inv'
      BY <1>A
    <2>1. CASE c_allocated + c_reserved + c_pending + a <= c_capacity
      BY <2>1 DEF TryAllocate
    <2>2. CASE ~(c_allocated + c_reserved + c_pending + a <= c_capacity)
      BY <2>2 DEF TryAllocate, vars
    <2> QED  BY <2>1, <2>2
  <1>B. CASE \E a \in 1..c_capacity : Reserve(a)
    <2> SUFFICES ASSUME NEW a \in 1..c_capacity, Reserve(a) PROVE Inv'
      BY <1>B
    <2>1. CASE c_allocated + c_reserved + c_pending + a <= c_capacity
      BY <2>1 DEF Reserve
    <2>2. CASE ~(c_allocated + c_reserved + c_pending + a <= c_capacity)
      BY <2>2 DEF Reserve, vars
    <2> QED  BY <2>1, <2>2
  <1>C. CASE \E a \in 1..c_reserved : CommitReservation(a)
    <2> SUFFICES ASSUME NEW a \in 1..c_reserved, CommitReservation(a) PROVE Inv'
      BY <1>C
    <2> QED  BY DEF CommitReservation
  <1>D. CASE \E a \in 1..c_allocated : Release(a)
    <2> SUFFICES ASSUME NEW a \in 1..c_allocated, Release(a) PROVE Inv'
      BY <1>D
    <2> QED  BY DEF Release
  <1>E. CASE \E a \in 1..c_allocated : MarkEviction(a)
    <2> SUFFICES ASSUME NEW a \in 1..c_allocated, MarkEviction(a) PROVE Inv'
      BY <1>E
    <2> QED  BY DEF MarkEviction
  <1>F. CASE \E a \in 1..c_pending : CompleteEviction(a)
    <2> SUFFICES ASSUME NEW a \in 1..c_pending, CompleteEviction(a) PROVE Inv'
      BY <1>F
    <2> QED  BY DEF CompleteEviction
  <1>X. CASE Next
    BY <1>X, <1>A, <1>B, <1>C, <1>D, <1>E, <1>F DEF Next
  <1> QED  BY <1>0, <1>X

THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv                    BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'     BY NextInv
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

\* Type preservation for every natural Capacity.
THEOREM TypeSafety == Spec => []TypeInvariant
  BY Safety, PTL DEF Inv

(*-------------------------------------------------------------------------*)
(* The refinement. No invariant is carried into it and none is needed: the  *)
(* substitution is a relabelling, so each step below is the target's own    *)
(* definition read under the new variable names.                           *)
(*-------------------------------------------------------------------------*)
LEMMA InitRefines == Init => BGT!Init
  BY DEF Init, BGT!Init

LEMMA NextRefines == [Next]_vars => [BGT!Next]_(BGT!vars)
  <1> SUFFICES ASSUME [Next]_vars PROVE [BGT!Next]_(BGT!vars)
    OBVIOUS
  <1>0. CASE UNCHANGED vars
    <2>1. UNCHANGED <<c_capacity, c_allocated, c_reserved, c_pending>>
      BY <1>0 DEF vars
    <2> QED  BY <2>1 DEF BGT!vars
  <1>X. CASE Next
    <2>A. CASE \E a \in 1..c_capacity : TryAllocate(a)
      <3> SUFFICES ASSUME NEW a \in 1..c_capacity, TryAllocate(a)
                   PROVE  BGT!Next
        BY <2>A
      <3>1. BGT!TryAllocate(a)
        BY DEF TryAllocate, BGT!TryAllocate, vars, BGT!vars
      <3> QED  BY <3>1 DEF BGT!Next
    <2>B. CASE \E a \in 1..c_capacity : Reserve(a)
      <3> SUFFICES ASSUME NEW a \in 1..c_capacity, Reserve(a)
                   PROVE  BGT!Next
        BY <2>B
      <3>1. BGT!Reserve(a)
        BY DEF Reserve, BGT!Reserve, vars, BGT!vars
      <3> QED  BY <3>1 DEF BGT!Next
    <2>C. CASE \E a \in 1..c_reserved : CommitReservation(a)
      <3> SUFFICES ASSUME NEW a \in 1..c_reserved, CommitReservation(a)
                   PROVE  BGT!Next
        BY <2>C
      <3>1. BGT!CommitReservation(a)
        BY DEF CommitReservation, BGT!CommitReservation
      <3> QED  BY <3>1 DEF BGT!Next
    <2>D. CASE \E a \in 1..c_allocated : Release(a)
      <3> SUFFICES ASSUME NEW a \in 1..c_allocated, Release(a)
                   PROVE  BGT!Next
        BY <2>D
      <3>1. BGT!Release(a)
        BY DEF Release, BGT!Release
      <3> QED  BY <3>1 DEF BGT!Next
    <2>E. CASE \E a \in 1..c_allocated : MarkEviction(a)
      <3> SUFFICES ASSUME NEW a \in 1..c_allocated, MarkEviction(a)
                   PROVE  BGT!Next
        BY <2>E
      <3>1. BGT!MarkEviction(a)
        BY DEF MarkEviction, BGT!MarkEviction
      <3> QED  BY <3>1 DEF BGT!Next
    <2>F. CASE \E a \in 1..c_pending : CompleteEviction(a)
      <3> SUFFICES ASSUME NEW a \in 1..c_pending, CompleteEviction(a)
                   PROVE  BGT!Next
        BY <2>F
      <3>1. BGT!CompleteEviction(a)
        BY DEF CompleteEviction, BGT!CompleteEviction
      <3> QED  BY <3>1 DEF BGT!Next
    <2> QED  BY <1>X, <2>A, <2>B, <2>C, <2>D, <2>E, <2>F DEF Next
  <1> QED  BY <1>0, <1>X

(*-------------------------------------------------------------------------*)
(* The pure-glue transition system refines Budget for every natural         *)
(* Capacity. All obligation-bearing state remains in the glue.              *)
(*-------------------------------------------------------------------------*)
THEOREM Refinement == Spec => BGT!Spec
  <1>1. Init => BGT!Init                                BY InitRefines
  <1>2. [Next]_vars => [BGT!Next]_(BGT!vars)            BY NextRefines
  <1> QED  BY <1>1, <1>2, PTL DEF Spec, BGT!Spec

\* Refinement under the base module's exported predicate.
THEOREM RefinementOriginal == Spec => BudgetRefinement
  BY Refinement DEF BudgetRefinement

====
