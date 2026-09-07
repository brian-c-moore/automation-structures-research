---- MODULE BudgetImplRefinesSpec ----
(*****************************************************************************)
(* Implementation-to-spec refinement for `Budget`.                           *)
(*                                                                           *)
(* This transition system is transcribed from the Verus contracts in         *)
(* `crate://automation-structures/0.2.3/src/primitives/budget.rs`, not from executable method    *)
(* bodies. Verus establishes that the bodies satisfy those contracts; this   *)
(* module establishes refinement from the contract-induced transitions to    *)
(* the canonical Budget specification.                                       *)
(*                                                                           *)
(* The contract-to-TLA+ transcription is a correspondence boundary, not a    *)
(* machine-checked translation. The field, guard, and effect mappings below  *)
(* state that boundary clause by clause.                                     *)
(*                                                                           *)
(* ==== STATE CORRESPONDENCE (Verus struct field <-> TLA+ variable) =========*)
(*                                                                           *)
(*   Verus `Budget` field   | TLA+ Budget variable | mapping                 *)
(*   -----------------------+----------------------+------------------------*)
(*   capacity: u64          | capacity             | identity                *)
(*   allocated: u64         | allocated            | identity                *)
(*   reserved: u64          | reserved             | identity                *)
(*   pending_eviction: u64  | pending_eviction     | identity                *)
(*                                                                           *)
(* The refinement mapping is the identity. The Verus struct carries exactly  *)
(* the specification's four variables under the same names; no projection,   *)
(* history variable, or auxiliary state is required.                         *)
(*                                                                           *)
(* Derived spec function:                                                    *)
(*   `Budget::used()`             ==  Used                (below)            *)
(*   `Budget::safety_invariant()` ==  SafetyInvariant     (below)            *)
(*                                                                           *)
(* ==== ACTION CORRESPONDENCE (guard and effect, per method) ================*)
(*                                                                           *)
(* Every mutating Verus method is represented by one action. Its guard is the *)
(* method's `requires` clause and its state relation is the `ensures` clause. *)
(*                                                                           *)
(*   Verus method            | this module          | TLA+ Budget action     *)
(*   ------------------------+----------------------+------------------------*)
(*   new(capacity)           | Init                 | Init                   *)
(*   try_allocate(amount)    | ImplTryAllocate      | TryAllocate            *)
(*   reserve(amount)         | ImplReserve          | Reserve                *)
(*   commit_reservation(a)   | ImplCommitReservation| CommitReservation      *)
(*   release(amount)         | ImplRelease          | Release                *)
(*   mark_eviction(amount)   | ImplMarkEviction     | MarkEviction           *)
(*   complete_eviction(a)    | ImplCompleteEviction | CompleteEviction       *)
(*   available()             | -- (see D3)          | -- (no counterpart)    *)
(*                                                                           *)
(* ==== DOMAIN AND SEMANTIC BOUNDARIES ====================================== *)
(*                                                                           *)
(* D1. Amount domain. The canonical spec's `Next` quantifies amounts over     *)
(*     `1..capacity` (allocate/reserve) or `1..reserved` / `1..allocated` /  *)
(*     `1..pending_eviction` (the rest), so zero is excluded everywhere and  *)
(*     over-capacity amounts are excluded from allocate/reserve.  The Verus  *)
(*     methods take `amount: u64` and impose no such bound.  This module     *)
(*     admits the full Verus domain (`Amounts == 0..MaxAmount`, with         *)
(*     MaxAmount > Capacity in the configuration so both excluded regions   *)
(*     are represented). Extra calls are stuttering steps of the canonical   *)
(*     specification,                                                        *)
(*     not new behaviour.  amount = 0 leaves every field unchanged in every  *)
(*     method; amount > capacity fails the ceiling test in try_allocate /    *)
(*     reserve and so takes their ELSE branch, also unchanged.  A step that  *)
(*     leaves `vars` unchanged is permitted by `[][Next]_vars`.  The         *)
(*     refinement therefore covers the wider implementation argument domain. *)
(*                                                                           *)
(* D2. u64 versus Nat. The specification variables are unbounded naturals;   *)
(*     implementation's are `u64`.  The Verus module lifts its specification *)
(*     arithmetic to `int` (`used()` returns `int`) and separately proves    *)
(*     every executable sum overflow-free from the safety invariant -- see   *)
(*     the `assert` lines in `available`, `commit_reservation` and           *)
(*     `mark_eviction`. Within states satisfying `safety_invariant()`, u64   *)
(*     arithmetic and integer arithmetic agree, so modelling the fields as   *)
(*     Nat here is faithful.  The premise of that agreement is itself        *)
(*     verified by Verus and is not an assumption of this TLA+ module.       *)
(*                                                                           *)
(* D3. `available()` has no specification action. It is a read-only          *)
(*     (`capacity - used`) that mutates nothing.                             *)
(*     projection and contributes no transition or refinement obligation.    *)
(*                                                                           *)
(* D4. The `requires safety_invariant()` precondition is carried as an        *)
(*     action guard.  In Rust it is the caller's proof obligation; here it   *)
(*     is a conjunct.  This is faithful in the strong direction: it can only *)
(*     remove implementation behaviors. Init establishes the invariant and   *)
(*     every action preserves it, so the guard is enabled in reachable states.*)
(*                                                                           *)
(* Control: BudgetImplRefinesSpec_NEG reverses the reservation transfer.      *)
(*****************************************************************************)
\* EXPECT: OK
EXTENDS Naturals

CONSTANTS
    Capacity,       \* the capacity argument passed to `Budget::new`
    MaxAmount       \* bound on the `amount: u64` argument (model bound only)

ASSUME CapacityType  == Capacity  \in Nat
ASSUME MaxAmountType == MaxAmount \in Nat

\* Bounded representation of the Verus u64 argument domain. It includes zero
\* and values above Capacity to exercise the D1 stuttering cases.
Amounts == 0..MaxAmount

VARIABLES capacity, allocated, reserved, pending_eviction

vars == <<capacity, allocated, reserved, pending_eviction>>

\* Verus `spec fn used(&self) -> int`.
Used == allocated + reserved + pending_eviction

\* Verus `spec fn safety_invariant(&self) -> bool`.
SafetyInvariant == Used <= capacity

TypeInvariant ==
    /\ capacity \in Nat
    /\ allocated \in Nat
    /\ reserved \in Nat
    /\ pending_eviction \in Nat

\* ---- Init: `pub fn new(capacity: u64) -> (b: Budget)` ---------------------
\* ensures b.capacity == capacity, b.allocated == 0, b.reserved == 0,
\*         b.pending_eviction == 0, b.safety_invariant()
Init ==
    /\ capacity = Capacity
    /\ allocated = 0
    /\ reserved = 0
    /\ pending_eviction = 0

\* ---- `try_allocate(&mut self, amount: u64) -> (ok: bool)` -----------------
\* requires old(self).safety_invariant()
\* ensures  capacity, reserved, pending_eviction unchanged
\*          safety_invariant()
\*          ok == (old.used() + amount <= old.capacity)
\*          ok  ==> allocated' == old.allocated + amount
\*          !ok ==> allocated' == old.allocated
ImplTryAllocate(amount) ==
    /\ SafetyInvariant
    /\ IF Used + amount <= capacity
       THEN allocated' = allocated + amount
       ELSE allocated' = allocated
    /\ UNCHANGED <<capacity, reserved, pending_eviction>>

\* ---- `reserve(&mut self, amount: u64) -> (ok: bool)` ----------------------
\* requires old(self).safety_invariant()
\* ensures  capacity, allocated, pending_eviction unchanged
\*          safety_invariant()
\*          ok == (old.used() + amount <= old.capacity)
\*          ok  ==> reserved' == old.reserved + amount
\*          !ok ==> reserved' == old.reserved
ImplReserve(amount) ==
    /\ SafetyInvariant
    /\ IF Used + amount <= capacity
       THEN reserved' = reserved + amount
       ELSE reserved' = reserved
    /\ UNCHANGED <<capacity, allocated, pending_eviction>>

\* ---- `commit_reservation(&mut self, amount: u64)` -------------------------
\* requires old(self).safety_invariant(), amount <= old(self).reserved
\* ensures  capacity, pending_eviction unchanged
\*          allocated' == old.allocated + amount
\*          reserved'  == old.reserved - amount
\*          safety_invariant()
ImplCommitReservation(amount) ==
    /\ SafetyInvariant
    /\ amount <= reserved
    /\ allocated' = allocated + amount
    /\ reserved' = reserved - amount
    /\ UNCHANGED <<capacity, pending_eviction>>

\* ---- `release(&mut self, amount: u64)` ------------------------------------
\* requires old(self).safety_invariant(), amount <= old(self).allocated
\* ensures  capacity, reserved, pending_eviction unchanged
\*          allocated' == old.allocated - amount
\*          safety_invariant()
ImplRelease(amount) ==
    /\ SafetyInvariant
    /\ amount <= allocated
    /\ allocated' = allocated - amount
    /\ UNCHANGED <<capacity, reserved, pending_eviction>>

\* ---- `mark_eviction(&mut self, amount: u64)` ------------------------------
\* requires old(self).safety_invariant(), amount <= old(self).allocated
\* ensures  capacity, reserved unchanged
\*          allocated'        == old.allocated - amount
\*          pending_eviction' == old.pending_eviction + amount
\*          safety_invariant()
ImplMarkEviction(amount) ==
    /\ SafetyInvariant
    /\ amount <= allocated
    /\ allocated' = allocated - amount
    /\ pending_eviction' = pending_eviction + amount
    /\ UNCHANGED <<capacity, reserved>>

\* ---- `complete_eviction(&mut self, amount: u64)` --------------------------
\* requires old(self).safety_invariant(), amount <= old(self).pending_eviction
\* ensures  capacity, allocated, reserved unchanged
\*          pending_eviction' == old.pending_eviction - amount
\*          safety_invariant()
ImplCompleteEviction(amount) ==
    /\ SafetyInvariant
    /\ amount <= pending_eviction
    /\ pending_eviction' = pending_eviction - amount
    /\ UNCHANGED <<capacity, allocated, reserved>>

Next ==
    \/ \E a \in Amounts : ImplTryAllocate(a)
    \/ \E a \in Amounts : ImplReserve(a)
    \/ \E a \in Amounts : ImplCommitReservation(a)
    \/ \E a \in Amounts : ImplRelease(a)
    \/ \E a \in Amounts : ImplMarkEviction(a)
    \/ \E a \in Amounts : ImplCompleteEviction(a)

Spec == Init /\ [][Next]_vars

\* ---- The refinement -------------------------------------------------------
\* Identity mapping (see the state-correspondence table above).  Written out
\* explicitly rather than left implicit so the mapping is legible at the site
\* that uses it.
B == INSTANCE Budget WITH
        Capacity         <- Capacity,
        capacity         <- capacity,
        allocated        <- allocated,
        reserved         <- reserved,
        pending_eviction <- pending_eviction

\* Every behavior admitted by the transcribed contracts must satisfy the
\* canonical Budget behavior specification.
Refinement == B!Spec

\* BudgetImplRefinesSpec_Proof proves Spec => Refinement for arbitrary natural
\* Capacity and MaxAmount.
====
