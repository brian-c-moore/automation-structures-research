---- MODULE RateLimitFromBudget_Proof ----
(***************************************************************************
  Parametric refinement proof for the Budget-and-clock construction.

  Refinement establishes Spec => RL!Spec. Capacity is a positive natural and
  WindowDuration is a natural. The step mapping itself does not use MaxClock's
  type, because the identical Tick guard transfers directly; the admitted
  RateLimit constant domain nevertheless retains MaxClock \in Nat.

  The clock is environment-provided, and the reset-plus-grant rollover is one
  atomic construction step.
 ***************************************************************************)
EXTENDS RateLimitFromBudget, TLAPS

ASSUME CapacityAss == Capacity \in Nat /\ Capacity >= 1
ASSUME WindowDurationAss == WindowDuration \in Nat

\* The construction's TypeInvariant is inductive on its own: it pins the
\* Budget fragment (reserved = pending_eviction = 0, allocated in
\* 0..Capacity) and types the windowing glue. BudgetSafety follows from it
\* as a corollary (allocated + 0 + 0 <= Capacity = capacity).
Inv == TypeInvariant

(*-------------------------------------------------------------------------*)
(* Lemma: Init establishes the inductive invariant.                        *)
(*-------------------------------------------------------------------------*)
LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv
    OBVIOUS
  <1> QED BY CapacityAss DEF Init, Inv, TypeInvariant

(*-------------------------------------------------------------------------*)
(* Lemma: every Next step preserves the inductive invariant.               *)
(*-------------------------------------------------------------------------*)
LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <1>c. /\ capacity = Capacity
        /\ allocated \in 0..Capacity
        /\ reserved = 0
        /\ pending_eviction = 0
        /\ window_start \in Nat
        /\ clock \in Nat
    BY DEF Inv, TypeInvariant
  <1>0. CASE UNCHANGED vars
    BY <1>0, <1>c DEF Inv, vars, TypeInvariant
  <1>1. CASE AcquireWithinWindow
    <2>a. /\ allocated < Capacity
          /\ allocated' = allocated + 1
          /\ UNCHANGED <<capacity, reserved, pending_eviction,
                         window_start, clock>>
      BY <1>1 DEF AcquireWithinWindow
    <2> QED BY <2>a, <1>c, CapacityAss DEF Inv, TypeInvariant
  <1>2. CASE AcquireFreshWindow
    <2>a. /\ allocated' = 1
          /\ window_start' = clock
          /\ UNCHANGED <<capacity, reserved, pending_eviction, clock>>
      BY <1>2 DEF AcquireFreshWindow
    <2> QED BY <2>a, <1>c, CapacityAss DEF Inv, TypeInvariant
  <1>3. CASE AcquireDenied
    <2>a. UNCHANGED vars
      BY <1>3 DEF AcquireDenied
    <2> QED BY <2>a, <1>c DEF Inv, vars, TypeInvariant
  <1>4. CASE Tick
    <2>a. /\ clock' = clock + 1
          /\ UNCHANGED <<capacity, allocated, reserved, pending_eviction,
                         window_start>>
      BY <1>4 DEF Tick
    <2> QED BY <2>a, <1>c DEF Inv, TypeInvariant
  <1> QED BY <1>0, <1>1, <1>2, <1>3, <1>4 DEF Next

(*-------------------------------------------------------------------------*)
(* Safety: the inductive invariant holds in every reachable state.         *)
(*-------------------------------------------------------------------------*)
THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv
    BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'
    BY NextInv
  <1> QED BY <1>1, <1>2, PTL DEF Spec

\* Construction invariants.
THEOREM TypeSafety == Spec => []TypeInvariant
  BY Safety, PTL DEF Inv

THEOREM BudgetSafetyPreservation == Spec => []BudgetSafety
  <1>1. Inv => BudgetSafety
    BY CapacityAss
       DEF Inv, TypeInvariant, BudgetSafety, Budget!SafetyInvariant
  <1> QED BY Safety, <1>1, PTL

(*-------------------------------------------------------------------------*)
(* The refinement: Init maps to RL!Init, every step maps to an RL step or  *)
(* an RL stutter.                                                          *)
(*-------------------------------------------------------------------------*)
LEMMA InitRefines == Init => RL!Init
  BY DEF Init, RL!Init

LEMMA NextRefines == Inv /\ [Next]_vars => [RL!Next]_(RL!vars)
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE [RL!Next]_(RL!vars)
    OBVIOUS
  <1>c. /\ capacity = Capacity
        /\ allocated \in 0..Capacity
        /\ reserved = 0
        /\ pending_eviction = 0
        /\ window_start \in Nat
        /\ clock \in Nat
    BY DEF Inv, TypeInvariant
  <1>0. CASE UNCHANGED vars
    <2>1. UNCHANGED <<allocated, window_start, clock>>
      BY <1>0 DEF vars
    <2> QED BY <2>1 DEF RL!vars
  <1>1. CASE AcquireWithinWindow
    \* Maps to RL!TryAcquire, within-window branch: the window-expiry test
    \* is false (from the guard, over typed arithmetic), room remains.
    <2>a. /\ clock - window_start < WindowDuration
          /\ allocated < Capacity
          /\ allocated' = allocated + 1
          /\ UNCHANGED <<capacity, reserved, pending_eviction,
                         window_start, clock>>
      BY <1>1 DEF AcquireWithinWindow
    <2>1. ~(clock - window_start >= WindowDuration)
      BY <2>a, <1>c, WindowDurationAss
    <2>2. RL!TryAcquire
      BY <2>a, <2>1 DEF RL!TryAcquire, RL!vars
    <2> QED BY <2>2 DEF RL!Next
  <1>2. CASE AcquireFreshWindow
    \* Maps to RL!TryAcquire, fresh-window branch: the expiry test is the
    \* guard verbatim.
    <2>a. /\ clock - window_start >= WindowDuration
          /\ allocated' = 1
          /\ window_start' = clock
          /\ UNCHANGED <<capacity, reserved, pending_eviction, clock>>
      BY <1>2 DEF AcquireFreshWindow
    <2>1. RL!TryAcquire
      BY <2>a DEF RL!TryAcquire, RL!vars
    <2> QED BY <2>1 DEF RL!Next
  <1>3. CASE AcquireDenied
    \* Denied acquisition leaves all six variables unchanged: an RL stutter.
    <2>a. UNCHANGED vars
      BY <1>3 DEF AcquireDenied
    <2>1. UNCHANGED <<allocated, window_start, clock>>
      BY <2>a DEF vars
    <2> QED BY <2>1 DEF RL!vars
  <1>4. CASE Tick
    <2>a. /\ clock < MaxClock
          /\ clock' = clock + 1
          /\ UNCHANGED <<capacity, allocated, reserved, pending_eviction,
                         window_start>>
      BY <1>4 DEF Tick
    <2>1. RL!Tick
      BY <2>a DEF RL!Tick
    <2> QED BY <2>1 DEF RL!Next
  <1> QED BY <1>0, <1>1, <1>2, <1>3, <1>4 DEF Next

(*-------------------------------------------------------------------------*)
(* The main result: the construction refines RateLimit, unbounded.         *)
(* Discharges the base module's Spec => RLRefinement claim.                *)
(*-------------------------------------------------------------------------*)
THEOREM Refinement == Spec => RL!Spec
  <1>1. Init => RL!Init
    BY InitRefines
  <1>2. Inv /\ [Next]_vars => [RL!Next]_(RL!vars)
    BY NextRefines
  <1>3. Spec => []Inv
    BY Safety
  <1> QED BY <1>1, <1>2, <1>3, PTL DEF Spec, RL!Spec

\* Restatement in the base module's own vocabulary.
THEOREM RefinementOriginal == Spec => RLRefinement
  BY Refinement DEF RLRefinement

====
