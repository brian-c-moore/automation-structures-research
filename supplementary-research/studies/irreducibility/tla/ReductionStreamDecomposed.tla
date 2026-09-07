----------------------- MODULE ReductionStreamDecomposed -----------------------
(* Irreducibility-by-construction for the concept-faithful ReductionStream.

   The reduction is split into (1) select an item, (2) combine it into the
   result, (3) remove it from remaining, with a CONCURRENT REDUCER that
   processes the same item before the removal. The set-based Reduction
   structure cannot host that counterexample at all: its `remaining` is a set
   drained by set-difference, so removal is idempotent and double-processing
   is UNREPRESENTABLE there.

   The three roles here are: Select stages the next element, Apply combines
   it and advances past it, and ConcurrentApply is the second reducer
   combining the SAME staged element before the advance.

   The split is arranged so that the intermediate state stays CONSISTENT --
   after Select, `result` and `pos` are both untouched, so AggregateCorrect
   still holds. The invariant is therefore asserted VERBATIM from the base
   module, with no quiescence guard, and the only way to break it is to count
   the same element twice.

   TLC must find a violation of AggregateCorrect: the item is counted twice.
   In loss computation that doubles a sample's contribution; in vote counting
   it counts a vote twice. Selection, combination, and removal are one atomic
   operation.                                                               *)
EXTENDS Naturals, Sequences

CONSTANTS Src, Op(_, _), Identity

OpImpl(a, b) == a + b
SrcImpl == <<3, 1, 2>>

FoldPrefix[n \in 0..Len(Src)] ==
    IF n = 0 THEN Identity ELSE Op(FoldPrefix[n - 1], Src[n])

VARIABLES result, pos,
          staged,   \* the element selected but not yet applied
          phase

vars == <<result, pos, staged, phase>>

TypeInvariant ==
    /\ pos \in 0..Len(Src)
    /\ result \in Nat
    /\ staged \in Nat
    /\ phase \in {"idle", "staged"}

\* The base module's obligation, verbatim.
AggregateCorrect ==
    result = FoldPrefix[pos]

Init ==
    /\ pos = 0
    /\ result = Identity
    /\ staged = 0
    /\ phase = "idle"

(* Step 1: select the next element. *)
Select ==
    /\ phase = "idle"
    /\ pos < Len(Src)
    /\ staged' = Src[pos + 1]
    /\ phase' = "staged"
    /\ UNCHANGED <<result, pos>>

(* Steps 2 and 3: combine it and advance past it. *)
Apply ==
    /\ phase = "staged"
    /\ result' = Op(result, staged)
    /\ pos' = pos + 1
    /\ phase' = "idle"
    /\ UNCHANGED staged

(* The concurrent reducer: a second reducer combines the SAME staged
   element before the primary has advanced past it. *)
ConcurrentApply ==
    /\ phase = "staged"
    /\ result' = Op(result, staged)
    /\ UNCHANGED <<pos, staged, phase>>

Next == Select \/ Apply \/ ConcurrentApply

Spec == Init /\ [][Next]_vars

\* TLC finds a violation of AggregateCorrect.
=============================================================================
