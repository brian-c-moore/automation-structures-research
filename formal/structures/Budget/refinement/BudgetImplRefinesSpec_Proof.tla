---- MODULE BudgetImplRefinesSpec_Proof ----
(***************************************************************************
  Parametric proof that the transition system transcribed from the Verus
  Budget contracts refines the canonical Budget specification:

      RefinementThm == Spec => B!Spec

  The theorem assumes only CapacityType and MaxAmountType inherited from
  BudgetImplRefinesSpec. The wider implementation argument domain
  (Amounts == 0..MaxAmount) is related to the canonical action domains by
  splitting each action into three cases:

      amount = 0             -> UNCHANGED vars, a canonical stutter
      amount >= 1, guard on  -> the canonical action at the SAME argument,
                                which requires showing the argument lands
                                inside the canonical quantifier's domain
      amount >= 1, guard off -> UNCHANGED vars, a canonical stutter

  For TryAllocate and Reserve, the canonical bound `a <= capacity` is not a
  contract guard; it follows from the successful ceiling test and natural
  typing of the existing usage fields. For the other four actions, the
  canonical bound is the transcribed Verus precondition.

  `available()` is read-only and contributes no transition. The transcribed
  safety precondition can only restrict behavior, and SafetyInvariantSafety
  proves that its premise holds throughout every reachable behavior.
 ***************************************************************************)
EXTENDS BudgetImplRefinesSpec, TLAPS

\* CapacityType and MaxAmountType are inherited from the base module.

(*-------------------------------------------------------------------------*)
(* The inductive invariant.                                                 *)
(*                                                                          *)
(* Typing supports natural-number subtraction. SafetyInvariant establishes   *)
(* that the transcribed contract precondition remains true in every reachable*)
(* state, although each mutating action also carries it as a guard.          *)
(*-------------------------------------------------------------------------*)
Inv == TypeInvariant /\ SafetyInvariant

(*-------------------------------------------------------------------------*)
(* Lemma: Init establishes the inductive invariant.                         *)
(*-------------------------------------------------------------------------*)
LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv
    OBVIOUS
  <1> QED
    BY CapacityType DEF Init, Inv, TypeInvariant, SafetyInvariant, Used

(*-------------------------------------------------------------------------*)
(* Lemma: every Next step preserves the inductive invariant.                *)
(*-------------------------------------------------------------------------*)
LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <1>c. /\ capacity \in Nat
        /\ allocated \in Nat
        /\ reserved \in Nat
        /\ pending_eviction \in Nat
        /\ allocated + reserved + pending_eviction <= capacity
    BY DEF Inv, TypeInvariant, SafetyInvariant, Used
  <1>0. CASE UNCHANGED vars
    BY <1>0, <1>c DEF Inv, vars, TypeInvariant, SafetyInvariant, Used
  <1>1. CASE \E a \in Amounts : ImplTryAllocate(a)
    <2> PICK a \in Amounts : ImplTryAllocate(a)
      BY <1>1
    <2>t. a \in Nat
      BY MaxAmountType DEF Amounts
    <2>e. /\ IF allocated + reserved + pending_eviction + a <= capacity
             THEN allocated' = allocated + a
             ELSE allocated' = allocated
          /\ UNCHANGED <<capacity, reserved, pending_eviction>>
      BY DEF ImplTryAllocate, Used
    <2> QED
      BY <2>e, <2>t, <1>c DEF Inv, TypeInvariant, SafetyInvariant, Used
  <1>2. CASE \E a \in Amounts : ImplReserve(a)
    <2> PICK a \in Amounts : ImplReserve(a)
      BY <1>2
    <2>t. a \in Nat
      BY MaxAmountType DEF Amounts
    <2>e. /\ IF allocated + reserved + pending_eviction + a <= capacity
             THEN reserved' = reserved + a
             ELSE reserved' = reserved
          /\ UNCHANGED <<capacity, allocated, pending_eviction>>
      BY DEF ImplReserve, Used
    <2> QED
      BY <2>e, <2>t, <1>c DEF Inv, TypeInvariant, SafetyInvariant, Used
  <1>3. CASE \E a \in Amounts : ImplCommitReservation(a)
    <2> PICK a \in Amounts : ImplCommitReservation(a)
      BY <1>3
    <2>t. a \in Nat
      BY MaxAmountType DEF Amounts
    <2>e. /\ a <= reserved
          /\ allocated' = allocated + a
          /\ reserved' = reserved - a
          /\ UNCHANGED <<capacity, pending_eviction>>
      BY DEF ImplCommitReservation
    <2> QED
      BY <2>e, <2>t, <1>c DEF Inv, TypeInvariant, SafetyInvariant, Used
  <1>4. CASE \E a \in Amounts : ImplRelease(a)
    <2> PICK a \in Amounts : ImplRelease(a)
      BY <1>4
    <2>t. a \in Nat
      BY MaxAmountType DEF Amounts
    <2>e. /\ a <= allocated
          /\ allocated' = allocated - a
          /\ UNCHANGED <<capacity, reserved, pending_eviction>>
      BY DEF ImplRelease
    <2> QED
      BY <2>e, <2>t, <1>c DEF Inv, TypeInvariant, SafetyInvariant, Used
  <1>5. CASE \E a \in Amounts : ImplMarkEviction(a)
    <2> PICK a \in Amounts : ImplMarkEviction(a)
      BY <1>5
    <2>t. a \in Nat
      BY MaxAmountType DEF Amounts
    <2>e. /\ a <= allocated
          /\ allocated' = allocated - a
          /\ pending_eviction' = pending_eviction + a
          /\ UNCHANGED <<capacity, reserved>>
      BY DEF ImplMarkEviction
    <2> QED
      BY <2>e, <2>t, <1>c DEF Inv, TypeInvariant, SafetyInvariant, Used
  <1>6. CASE \E a \in Amounts : ImplCompleteEviction(a)
    <2> PICK a \in Amounts : ImplCompleteEviction(a)
      BY <1>6
    <2>t. a \in Nat
      BY MaxAmountType DEF Amounts
    <2>e. /\ a <= pending_eviction
          /\ pending_eviction' = pending_eviction - a
          /\ UNCHANGED <<capacity, allocated, reserved>>
      BY DEF ImplCompleteEviction
    <2> QED
      BY <2>e, <2>t, <1>c DEF Inv, TypeInvariant, SafetyInvariant, Used
  <1> QED
    BY <1>0, <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

(*-------------------------------------------------------------------------*)
(* Safety: the inductive invariant holds in every reachable state.          *)
(*-------------------------------------------------------------------------*)
THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv
    BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'
    BY NextInv
  <1> QED BY <1>1, <1>2, PTL DEF Spec

\* Type and capacity preservation for arbitrary natural constants.
THEOREM TypeSafety == Spec => []TypeInvariant
  BY Safety, PTL DEF Inv

THEOREM SafetyInvariantSafety == Spec => []SafetyInvariant
  BY Safety, PTL DEF Inv

(*-------------------------------------------------------------------------*)
(* The refinement: Init maps to B!Init, every step maps to a Budget step or *)
(* a Budget stutter.                                                        *)
(*                                                                          *)
(* The mapping is the identity (state-correspondence table in the base       *)
(* module), so B!vars is literally vars and B!Init is literally Init.  Those *)
(* two facts follow directly from the INSTANCE substitution list.           *)
(*-------------------------------------------------------------------------*)
\* Action-level equality is required because each stuttering branch uses the
\* primed relation; the unprimed state equation alone is insufficient.
LEMMA StutterTransfer == UNCHANGED vars => UNCHANGED B!vars
  BY DEF vars, B!vars

LEMMA InitRefines == Init => B!Init
  BY DEF Init, B!Init

LEMMA NextRefines == Inv /\ [Next]_vars => [B!Next]_(B!vars)
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE [B!Next]_(B!vars)
    OBVIOUS
  <1>c. /\ capacity \in Nat
        /\ allocated \in Nat
        /\ reserved \in Nat
        /\ pending_eviction \in Nat
        /\ allocated + reserved + pending_eviction <= capacity
    BY DEF Inv, TypeInvariant, SafetyInvariant, Used
  <1>0. CASE UNCHANGED vars
    BY <1>0, StutterTransfer
  \* --- try_allocate ------------------------------------------------------
  <1>1. CASE \E a \in Amounts : ImplTryAllocate(a)
    <2> PICK a \in Amounts : ImplTryAllocate(a)
      BY <1>1
    <2>t. a \in Nat
      BY MaxAmountType DEF Amounts
    <2>e. /\ IF allocated + reserved + pending_eviction + a <= capacity
             THEN allocated' = allocated + a
             ELSE allocated' = allocated
          /\ UNCHANGED <<capacity, reserved, pending_eviction>>
      BY DEF ImplTryAllocate, Used
    <2>1. CASE a = 0
      \* D1's zero case: the contract admits amount = 0, the canonical
      \* quantifier starts at 1, and the step moves nothing.
      <3>1. UNCHANGED vars
        BY <2>e, <2>1, <1>c DEF vars
      <3> QED BY <3>1, StutterTransfer
    <2>2. CASE a # 0 /\ allocated + reserved + pending_eviction + a <= capacity
      \* For a non-stuttering step, a <= capacity follows from the
      \* ceiling test plus the typing of the three usage fields.
      <3>1. a \in 1..capacity
        BY <2>2, <2>t, <1>c
      <3>2. B!TryAllocate(a)
        BY <2>e, <2>2 DEF B!TryAllocate
      <3> QED BY <3>1, <3>2 DEF B!Next
    <2>3. CASE a # 0 /\ ~(allocated + reserved + pending_eviction + a <= capacity)
      \* D1's over-capacity case: the ELSE branch frames every variable.
      <3>1. UNCHANGED vars
        BY <2>e, <2>3 DEF vars
      <3> QED BY <3>1, StutterTransfer
    <2> QED BY <2>1, <2>2, <2>3
  \* --- reserve -----------------------------------------------------------
  <1>2. CASE \E a \in Amounts : ImplReserve(a)
    <2> PICK a \in Amounts : ImplReserve(a)
      BY <1>2
    <2>t. a \in Nat
      BY MaxAmountType DEF Amounts
    <2>e. /\ IF allocated + reserved + pending_eviction + a <= capacity
             THEN reserved' = reserved + a
             ELSE reserved' = reserved
          /\ UNCHANGED <<capacity, allocated, pending_eviction>>
      BY DEF ImplReserve, Used
    <2>1. CASE a = 0
      <3>1. UNCHANGED vars
        BY <2>e, <2>1, <1>c DEF vars
      <3> QED BY <3>1, StutterTransfer
    <2>2. CASE a # 0 /\ allocated + reserved + pending_eviction + a <= capacity
      <3>1. a \in 1..capacity
        BY <2>2, <2>t, <1>c
      <3>2. B!Reserve(a)
        BY <2>e, <2>2 DEF B!Reserve
      <3> QED BY <3>1, <3>2 DEF B!Next
    <2>3. CASE a # 0 /\ ~(allocated + reserved + pending_eviction + a <= capacity)
      <3>1. UNCHANGED vars
        BY <2>e, <2>3 DEF vars
      <3> QED BY <3>1, StutterTransfer
    <2> QED BY <2>1, <2>2, <2>3
  \* --- commit_reservation ------------------------------------------------
  <1>3. CASE \E a \in Amounts : ImplCommitReservation(a)
    <2> PICK a \in Amounts : ImplCommitReservation(a)
      BY <1>3
    <2>t. a \in Nat
      BY MaxAmountType DEF Amounts
    <2>e. /\ a <= reserved
          /\ allocated' = allocated + a
          /\ reserved' = reserved - a
          /\ UNCHANGED <<capacity, pending_eviction>>
      BY DEF ImplCommitReservation
    <2>1. CASE a = 0
      <3>1. UNCHANGED vars
        BY <2>e, <2>1, <1>c DEF vars
      <3> QED BY <3>1, StutterTransfer
    <2>2. CASE a # 0
      \* The canonical domain bound is the transcribed Verus precondition.
      <3>1. a \in 1..reserved
        BY <2>e, <2>2, <2>t, <1>c
      <3>2. B!CommitReservation(a)
        BY <2>e DEF B!CommitReservation
      <3> QED BY <3>1, <3>2 DEF B!Next
    <2> QED BY <2>1, <2>2
  \* --- release -----------------------------------------------------------
  <1>4. CASE \E a \in Amounts : ImplRelease(a)
    <2> PICK a \in Amounts : ImplRelease(a)
      BY <1>4
    <2>t. a \in Nat
      BY MaxAmountType DEF Amounts
    <2>e. /\ a <= allocated
          /\ allocated' = allocated - a
          /\ UNCHANGED <<capacity, reserved, pending_eviction>>
      BY DEF ImplRelease
    <2>1. CASE a = 0
      <3>1. UNCHANGED vars
        BY <2>e, <2>1, <1>c DEF vars
      <3> QED BY <3>1, StutterTransfer
    <2>2. CASE a # 0
      <3>1. a \in 1..allocated
        BY <2>e, <2>2, <2>t, <1>c
      <3>2. B!Release(a)
        BY <2>e DEF B!Release
      <3> QED BY <3>1, <3>2 DEF B!Next
    <2> QED BY <2>1, <2>2
  \* --- mark_eviction -----------------------------------------------------
  <1>5. CASE \E a \in Amounts : ImplMarkEviction(a)
    <2> PICK a \in Amounts : ImplMarkEviction(a)
      BY <1>5
    <2>t. a \in Nat
      BY MaxAmountType DEF Amounts
    <2>e. /\ a <= allocated
          /\ allocated' = allocated - a
          /\ pending_eviction' = pending_eviction + a
          /\ UNCHANGED <<capacity, reserved>>
      BY DEF ImplMarkEviction
    <2>1. CASE a = 0
      <3>1. UNCHANGED vars
        BY <2>e, <2>1, <1>c DEF vars
      <3> QED BY <3>1, StutterTransfer
    <2>2. CASE a # 0
      <3>1. a \in 1..allocated
        BY <2>e, <2>2, <2>t, <1>c
      <3>2. B!MarkEviction(a)
        BY <2>e DEF B!MarkEviction
      <3> QED BY <3>1, <3>2 DEF B!Next
    <2> QED BY <2>1, <2>2
  \* --- complete_eviction -------------------------------------------------
  <1>6. CASE \E a \in Amounts : ImplCompleteEviction(a)
    <2> PICK a \in Amounts : ImplCompleteEviction(a)
      BY <1>6
    <2>t. a \in Nat
      BY MaxAmountType DEF Amounts
    <2>e. /\ a <= pending_eviction
          /\ pending_eviction' = pending_eviction - a
          /\ UNCHANGED <<capacity, allocated, reserved>>
      BY DEF ImplCompleteEviction
    <2>1. CASE a = 0
      <3>1. UNCHANGED vars
        BY <2>e, <2>1, <1>c DEF vars
      <3> QED BY <3>1, StutterTransfer
    <2>2. CASE a # 0
      <3>1. a \in 1..pending_eviction
        BY <2>e, <2>2, <2>t, <1>c
      <3>2. B!CompleteEviction(a)
        BY <2>e DEF B!CompleteEviction
      <3> QED BY <3>1, <3>2 DEF B!Next
    <2> QED BY <2>1, <2>2
  <1> QED
    BY <1>0, <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

(*-------------------------------------------------------------------------*)
(* The contract-derived transition system refines canonical Budget for every*)
(* natural Capacity and MaxAmount.                                          *)
(*-------------------------------------------------------------------------*)
THEOREM RefinementThm == Spec => B!Spec
  <1>1. Init => B!Init
    BY InitRefines
  <1>2. Inv /\ [Next]_vars => [B!Next]_(B!vars)
    BY NextRefines
  <1>3. Spec => []Inv
    BY Safety
  <1> QED BY <1>1, <1>2, <1>3, PTL DEF Spec, B!Spec

\* Refinement under the base module's exported predicate.
THEOREM RefinementOriginal == Spec => Refinement
  BY RefinementThm DEF Refinement

====
